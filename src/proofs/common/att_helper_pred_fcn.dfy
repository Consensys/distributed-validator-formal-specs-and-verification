include "../../common/commons.dfy"
include "../../specs/dvc/dvc_attestation_creation.dfy"
include "../../specs/consensus/consensus.dfy"
include "../../specs/network/network.dfy"
include "../../specs/dv/dv_attestation_creation.dfy"
include "../common/helper_sets_lemmas.dfy"
include "../no_slashable_attestations/common/dvc_attestation_creation_instrumented.dfy"

module Att_Helper_Pred_Fcn
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened Att_DVC_Spec
    import opened Att_DV
    import opened Helper_Sets_Lemmas
    import opened BN_Axioms
    import opened RS_Axioms
    import Att_DVC_Spec_NonInstr

    function f_new_process_after_updateConsensusInstanceValidityCheck(
        process: Att_DVCState,
        attestation_duty: AttestationDuty
    ): Att_DVCState
    requires attestation_duty.slot in process.future_att_consensus_instances_already_decided.Keys 
    {
        var new_attestation_slashing_db := 
                f_update_attestation_slashing_db(
                    process.attestation_slashing_db, 
                    process.future_att_consensus_instances_already_decided[attestation_duty.slot]
                );
                
        var new_process := 
                process.(
                    future_att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided - {attestation_duty.slot},
                    attestation_slashing_db := new_attestation_slashing_db,
                    attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                        process.attestation_consensus_engine_state,
                        new_attestation_slashing_db
                    )                        
                );

        new_process
    }

    function f_new_process_after_starting_new_att_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty
    ): Att_DVCState
    requires attestation_duty.slot !in process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
    requires || !process.latest_attestation_duty.isPresent()
             || process.latest_attestation_duty.safe_get().slot < attestation_duty.slot
    {
        process.( current_attestation_duty := Some(attestation_duty),
                  latest_attestation_duty := Some(attestation_duty),
                  attestation_consensus_engine_state := startConsensusInstance(
                    process.attestation_consensus_engine_state,
                    attestation_duty.slot,
                    attestation_duty,
                    process.attestation_slashing_db
                )
        )
    }

    predicate is_correct_att_share(
        s: Att_DVState,
        hn: BLSPubkey,
        att_share: AttestationShare
    )
    {
        && hn in s.honest_nodes_states.Keys 
        && att_share in s.att_network.allMessagesSent
        && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));
        && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
        && verify_bls_signature(attestation_signing_root, att_share.signature, hn)   
    }
    
    predicate is_decided_data_for_current_slot(
        process: Att_DVCState,
        decided_attestation_data: AttestationData,
        id: Slot
    )
    {
        && process.current_attestation_duty.isPresent()
        && id == process.current_attestation_duty.safe_get().slot
        && id == decided_attestation_data.slot
    }

    predicate pred_att_duty_was_already_decided(
        process: Att_DVCState,
        id: Slot
    ) 
    {
        && process.current_attestation_duty.isPresent()
        && id == process.current_attestation_duty.safe_get().slot 
    }

    predicate pred_decision_of_att_duty_was_known(
        process: Att_DVCState,
        attestation_duty: AttestationDuty
    ) 
    {
        attestation_duty.slot in process.future_att_consensus_instances_already_decided.Keys 
    }

    function f_update_process_after_att_duty_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData
    ) : (ret_process: Att_DVCState)
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

    predicate no_curr_duty(s_mod: Att_DVCState) 
    {
        && !s_mod.current_attestation_duty.isPresent()   
    }

    
    
    predicate pred_listen_for_attestation_shares_checker(
        process: Att_DVCState,
        attestation_share: AttestationShare
    ) 
    {
        && var activate_att_consensus_intances := process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;
        && (
            || (activate_att_consensus_intances == {} && !process.latest_attestation_duty.isPresent())
            || (activate_att_consensus_intances != {} && minInSet(activate_att_consensus_intances) <= attestation_share.data.slot)
            || (activate_att_consensus_intances == {} && !process.current_attestation_duty.isPresent() && process.latest_attestation_duty.isPresent() && process.latest_attestation_duty.safe_get().slot < attestation_share.data.slot)
        )
    }

    function f_add_new_attestation_share(
        process: Att_DVCState,
        attestation_share: AttestationShare
    ): Att_DVCState
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
        process: Att_DVCState,
        aggregated_attestation: Attestation
    ): Att_DVCState

    {
        process.(
            bn := process.bn.(
                submitted_data := process.bn.submitted_data + [aggregated_attestation]
            )
        )
    }

    function f_stopConsensusInstances_after_receiving_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock
    ): Att_DVCState
    requires block.body.state_root in process.bn.state_roots_of_imported_blocks
    requires    var valIndex := bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);
                forall a1, a2 | 
                        && a1 in block.body.attestations
                        && Att_DVC_Spec_NonInstr.isMyAttestation(a1, process.bn, block, valIndex)
                        && a2 in block.body.attestations
                        && Att_DVC_Spec_NonInstr.isMyAttestation(a2, process.bn, block, valIndex)                        
                    ::
                        a1.data.slot == a2.data.slot ==> a1 == a2  
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
        process: Att_DVCState,
        att_consensus_instances_already_decided: map<Slot, AttestationData>
    )
    {
        && process.current_attestation_duty.isPresent() 
        && process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided 
    } 

    function f_updateConsensusInstanceValidityCheck_in_listen_for_new_imported_blocks(
        process: Att_DVCState,
        att_consensus_instances_already_decided: map<Slot, AttestationData>
    ): Att_DVCState
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

    predicate nonempty_latest_att_duty(s: Att_DVCState) 
    {
        && s.latest_attestation_duty.isPresent()  
    }
}