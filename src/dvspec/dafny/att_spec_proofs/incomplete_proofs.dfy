include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"
include "../att_spec_proofs/fnc_inv.dfy"
include "../att_spec_proofs/dvn_next_inv.dfy"
include "../att_spec_proofs/helper_sets_lemmas.dfy"


module Incomplete_Proofs 
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB    
    import opened Helper_Sets_Lemmas
    import opened DVN_Next_Inv
    import opened Fnc_Inv    

    lemma lemma_f_serve_attestation_duty_inv4(
        dvc: DVCNodeState,
        attestation_duty: AttestationDuty,
        dvc': DVCNodeState
    )  
    requires f_serve_attestation_duty.requires(dvc, attestation_duty)
    requires dvc' == f_serve_attestation_duty(dvc, attestation_duty).state
    ensures dvc'.all_rcvd_duties == dvc.all_rcvd_duties + {attestation_duty}    
    {
        var dvc_mod := dvc.(
                attestation_duties_queue := dvc.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := dvc.all_rcvd_duties + {attestation_duty}
            );        

        lemma_f_check_for_next_queued_duty_inv3(dvc_mod, dvc');        
    }

    lemma lemma_f_check_for_next_queued_duty_inv3(
        dvc: DVCNodeState,
        dvc': DVCNodeState
    )
    requires f_check_for_next_queued_duty.requires(dvc)
    requires dvc' == f_check_for_next_queued_duty(dvc).state
    ensures dvc'.all_rcvd_duties == dvc.all_rcvd_duties
    decreases dvc.attestation_duties_queue
    {
        if  && dvc.attestation_duties_queue != [] 
            && (
                || dvc.attestation_duties_queue[0].slot in dvc.future_att_consensus_instances_already_decided
                || !dvc.current_attestation_duty.isPresent()
            )    
        {            
                if dvc.attestation_duties_queue[0].slot in dvc.future_att_consensus_instances_already_decided.Keys 
                {
                    var queue_head := dvc.attestation_duties_queue[0];
                    var new_attestation_slashing_db := f_update_attestation_slashing_db(dvc.attestation_slashing_db, dvc.future_att_consensus_instances_already_decided[queue_head.slot]);
                    var dvc_mod := dvc.(
                        attestation_duties_queue := dvc.attestation_duties_queue[1..],
                        future_att_consensus_instances_already_decided := dvc.future_att_consensus_instances_already_decided - {queue_head.slot},
                        attestation_slashing_db := new_attestation_slashing_db,
                        attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                            dvc.attestation_consensus_engine_state,
                            new_attestation_slashing_db
                        )                        
                    );
                    lemma_f_check_for_next_queued_duty_inv3(dvc_mod, dvc');
                }
                else
                { 
                    var dvc_mod := dvc.(
                        attestation_duties_queue := dvc.attestation_duties_queue[1..]
                    );         
                    lemma_f_start_next_duty_inv3(dvc_mod, dvc.attestation_duties_queue[0], dvc');
                }
        }
        else
        { 
            assert dvc'.all_rcvd_duties == dvc.all_rcvd_duties;
        }
    }

    lemma lemma_f_start_next_duty_inv3(dvc: DVCNodeState, attestation_duty: AttestationDuty, dvc': DVCNodeState)
    requires f_start_next_duty.requires(dvc, attestation_duty)
    requires dvc' == f_start_next_duty(dvc, attestation_duty).state
    ensures dvc'.all_rcvd_duties == dvc.all_rcvd_duties        
    {  
        assert dvc'.all_rcvd_duties == dvc.all_rcvd_duties;
    }  

    lemma lemma_f_att_consensus_decided_inv3(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCNodeState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state 
    ensures process'.all_rcvd_duties == process.all_rcvd_duties
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

        var process_mod := 
            process.(
                current_attestation_duty := None,
                attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                attestation_slashing_db := attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    process.attestation_consensus_engine_state,
                    attestation_slashing_db
                )
            );

        var ret_check_for_next_queued_duty := f_check_for_next_queued_duty(process_mod);
        
        lemma_f_check_for_next_queued_duty_inv3(process_mod, ret_check_for_next_queued_duty.state);

        assert process' == ret_check_for_next_queued_duty.state;
        
    }  


    lemma lemma_f_listen_for_attestation_shares_inv3(
        process: DVCNodeState,
        attestation_share: AttestationShare,
        process': DVCNodeState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    ensures process.all_rcvd_duties == process'.all_rcvd_duties
    {}

    lemma lemma_f_listen_for_new_imported_blocks_inv3(
        process: DVCNodeState,
        block: BeaconBlock,
        process': DVCNodeState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    ensures process.all_rcvd_duties == process'.all_rcvd_duties
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var process :=
                process.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );                    

        if process.current_attestation_duty.isPresent() && process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            var decided_attestation_data := att_consensus_instances_already_decided[process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);
            var process := process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    process.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );
            lemma_f_check_for_next_queued_duty_inv3(process, process');
        }
        else
        {}
    }    
}