include "../../common/commons.dfy"
include "../../specs/dvc/dvc_attestation_creation.dfy"
include "../../specs/consensus/consensus.dfy"
include "../../specs/network/network.dfy"
include "../../specs/dv/dv_attestation_creation.dfy"
include "../common/helper_sets_lemmas.dfy"
include "../no_slashable_attestations/common/attestation_creation_instrumented.dfy"
include "../no_slashable_attestations/supporting_lemmas/inv.dfy"

module Helper_Pred_Fcn
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Helper_Sets_Lemmas
    import opened DVC_Spec_Axioms
    import DVC_Spec_NonInstr
    
    predicate first_queued_att_duty_was_decided_or_ready_to_be_served(process: DVCState) 
    {
        && process.attestation_duties_queue != [] 
        &&  (
                || process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided
                || !process.current_attestation_duty.isPresent()
            ) 
    }

    predicate first_queued_att_duty_was_decided(process: DVCState)
    {
        process.attestation_duties_queue != [] 
        ==>
        process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided.Keys
    }

    function f_dequeue_attestation_duties_queue(process: DVCState)
        : (ret_process: DVCState)
    requires first_queued_att_duty_was_decided_or_ready_to_be_served(process)
    requires first_queued_att_duty_was_decided(process)
    ensures |ret_process.attestation_duties_queue| < |process.attestation_duties_queue|
    {
        var queue_head := process.attestation_duties_queue[0];
        var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, process.future_att_consensus_instances_already_decided[queue_head.slot]);
        var ret_process := 
            process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..],
                        future_att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided - {queue_head.slot},
                        attestation_slashing_db := new_attestation_slashing_db,
                        attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                            process.attestation_consensus_engine_state,
                            new_attestation_slashing_db
                        )
            );
        ret_process
    }

    function f_dequeue_first_queued_att_duty(process: DVCState)
        : (ret_process: DVCState)
    requires first_queued_att_duty_was_decided_or_ready_to_be_served(process)
    ensures |ret_process.attestation_duties_queue| < |process.attestation_duties_queue|
    {
        var ret_process := 
            process.(
                attestation_duties_queue := process.attestation_duties_queue[1..]
            );   
        ret_process
    }

    function f_enqueue_new_att_duty(
        process: DVCState,
        attestation_duty: AttestationDuty
    ) : (ret_process: DVCState)
    {
        var ret_process := 
            process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );  
        ret_process
    }

    predicate pred_curr_att_duty_has_been_decided(
        process: DVCState,
        id: Slot) 
    {
        && process.current_attestation_duty.isPresent()
        && id == process.current_attestation_duty.safe_get().slot
    }

    function f_update_process_after_att_duty_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData
    ) : (ret_process: DVCState)
    requires && process.current_attestation_duty.isPresent()
             && id == process.current_attestation_duty.safe_get().slot
    {
        var local_current_attestation_duty := process.current_attestation_duty.safe_get();
        var attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);

        var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
        var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
        var attestation_signature_share := rs_sign_attestation(decided_attestation_data, fork_version, attestation_signing_root, process.rs);
        var attestation_with_signature_share := AttestationShare(
                aggregation_bits := get_aggregation_bits(local_current_attestation_duty.validator_index),
                data := decided_attestation_data, 
                signature := attestation_signature_share
            ); 

        var ret_process := 
            process.(
                current_attestation_duty := None,
                attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                attestation_slashing_db := attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    process.attestation_consensus_engine_state,
                    attestation_slashing_db
                )
            );

        ret_process
    }

    predicate no_curr_duty_and_nonempty_duty_queue(s_mod: DVCState) 
    {
        && |s_mod.attestation_duties_queue| > 0 
        && !s_mod.current_attestation_duty.isPresent()   
    }

    function f_add_new_att_duty_to_the_queue(
        process: DVCState,
        attestation_duty: AttestationDuty
    ): DVCState
    {
        process.(
            attestation_duties_queue := process.attestation_duties_queue + [attestation_duty]
        )        
    } 
    
    predicate pred_listen_for_attestation_shares_checker(
        process: DVCState,
        attestation_share: AttestationShare
    ) 
    {
        && var activate_att_consensus_intances := process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;
        && (
            || (activate_att_consensus_intances == {} && !process.latest_attestation_duty.isPresent())
            || (activate_att_consensus_intances != {} && minInSet(activate_att_consensus_intances) <= attestation_share.data.slot)
            || (activate_att_consensus_intances == {} && process.current_attestation_duty.isPresent() && process.current_attestation_duty.safe_get().slot <= attestation_share.data.slot)                
            || (activate_att_consensus_intances == {} && !process.current_attestation_duty.isPresent() && process.latest_attestation_duty.isPresent() && process.latest_attestation_duty.safe_get().slot < attestation_share.data.slot)
        )
    }

    function f_add_new_attestation_share(
        process: DVCState,
        attestation_share: AttestationShare
    ): DVCState
    requires pred_listen_for_attestation_shares_checker(
                process,
                attestation_share) 
    {
        var activate_att_consensus_intances := process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

        var k := (attestation_share.data, attestation_share.aggregation_bits);
        var attestation_shares_db_at_slot := getOrDefault(process.rcvd_attestation_shares, attestation_share.data.slot, map[]);
        
        var new_attestation_shares_db := 
                process.rcvd_attestation_shares[
                    attestation_share.data.slot := 
                        attestation_shares_db_at_slot[
                                    k := 
                                        getOrDefault(attestation_shares_db_at_slot, k, {}) + 
                                        {attestation_share}
                                    ]
                        ];

        var ret_process := process.(
            rcvd_attestation_shares := new_attestation_shares_db
        );

        ret_process
    }

    function f_add_new_submitted_attestation(
        process: DVCState,
        aggregated_attestation: Attestation
    ): DVCState

    {
        process.(
            bn := process.bn.(
                attestations_submitted := process.bn.attestations_submitted + [aggregated_attestation]
            )
        )
    }

    function f_stopConsensusInstances_after_receiving_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock
    ): DVCState
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var ret_process :=
                process.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );    

        ret_process  
    }

    predicate pred_listen_for_new_imported_blocks_checker(
        process: DVCState,
        att_consensus_instances_already_decided: map<Slot, AttestationData>
    )
    {
        && process.current_attestation_duty.isPresent() 
        && process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided 
    } 

    function f_updateConsensusInstanceValidityCheck_in_listen_for_new_imported_blocks(
        process: DVCState,
        att_consensus_instances_already_decided: map<Slot, AttestationData>
    ): DVCState
    requires pred_listen_for_new_imported_blocks_checker(process, att_consensus_instances_already_decided)
    {
        var decided_attestation_data := att_consensus_instances_already_decided[process.current_attestation_duty.safe_get().slot];
        var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);
        var ret_process := process.(
            current_attestation_duty := None,
            attestation_slashing_db := new_attestation_slashing_db,
            attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                process.attestation_consensus_engine_state,
                new_attestation_slashing_db
            )                
        );
        ret_process
    }   

    predicate latest_att_duty_and_nonempty_duty_queue(s: DVCState) 
    {
        && |s.attestation_duties_queue| > 0 
        && s.latest_attestation_duty.isPresent()  
    }
}