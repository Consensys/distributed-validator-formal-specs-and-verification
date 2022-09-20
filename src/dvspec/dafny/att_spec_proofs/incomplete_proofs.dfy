include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"
include "../att_spec_proofs/fnc_inv.dfy"
include "../att_spec_proofs/dvn_next_invs_1_7.dfy"
include "../att_spec_proofs/dvn_next_invs_8_18.dfy"
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
    import opened DVN_Next_Invs_1_7
    import opened DVN_Next_Invs_8_18
    import opened Fnc_Inv    

    lemma {:axiom} axiom_inv23(dvn: DVState)    
    ensures inv23(dvn)

    lemma lemma_inv23_add_block_to_bn(
        s: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)    
    requires inv23_body(s)
    ensures inv23_body(s')
    { }

    lemma lemma_inv23_f_listen_for_attestation_shares(
        process: DVCNodeState,
        attestation_share: AttestationShare,
        process': DVCNodeState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv23_body(process)
    ensures inv23_body(process')
    {}

    lemma lemma_inv23_f_resend_attestation_share(
        process: DVCNodeState,
        process': DVCNodeState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv23_body(process)
    ensures inv23_body(process')
    { } 

    lemma lemma_inv23_f_check_for_next_queued_duty(
        process: DVCNodeState,
        process': DVCNodeState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state    
    requires inv17_body(process)
    requires inv23_body(process)
    ensures inv23_body(process')
    decreases process.attestation_duties_queue
    {
        if  && process.attestation_duties_queue != [] 
            && (
                || process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided
                || !process.current_attestation_duty.isPresent()
            )    
        {            
                if process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided.Keys 
                {
                    var queue_head := process.attestation_duties_queue[0];
                    var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, process.future_att_consensus_instances_already_decided[queue_head.slot]);
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..],
                        future_att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided - {queue_head.slot},
                        attestation_slashing_db := new_attestation_slashing_db,
                        attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                            process.attestation_consensus_engine_state,
                            new_attestation_slashing_db
                        )                        
                    );
                    lemma_inv23_f_check_for_next_queued_duty(process_mod, process');
                }
                else
                { 
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    );     
                    assert inv23_body(process_mod);

                    lemma_inv23_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
                }
        }
        else
        { 
            assert process'.all_rcvd_duties == process.all_rcvd_duties;
        }
    }

    lemma lemma_inv23_f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCNodeState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv23_body(process)
    ensures inv23_body(process')
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

        var process := 
            process.(
                current_attestation_duty := None,
                attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                attestation_slashing_db := attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    process.attestation_consensus_engine_state,
                    attestation_slashing_db
                )
            );

    
        assert inv23_body(process);

        var ret_check_for_next_queued_duty := f_check_for_next_queued_duty(process);
        
        lemma_inv23_f_check_for_next_queued_duty(process, ret_check_for_next_queued_duty.state);

        assert process' == ret_check_for_next_queued_duty.state;        
    } 
    
    lemma lemma_inv23_f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock,
        process': DVCNodeState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv23_body(process)
    ensures inv23_body(process')
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
        
        assert inv23_body(process);

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
            
            assert inv23_body(process);

            lemma_inv23_f_check_for_next_queued_duty(process, process');
        }
        else
        {               
            assert inv23_body(process);
        }
    } 

    lemma lemma_inv23_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        process': DVCNodeState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv23_body(process)
    ensures inv23_body(process')
    {
        var process_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );        
        
        lemma_inv23_f_check_for_next_queued_duty(process_mod, process');        
    } 
    

    lemma lemma_inv23_f_start_next_duty(process: DVCNodeState, attestation_duty: AttestationDuty, process': DVCNodeState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires inv23_body(process)
    // requires inv17_body(process)
    requires ( forall k: Slot | k in process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys ::
                    k < attestation_duty.slot
            )
    // ensures inv17_body'(process')
    ensures inv23_body(process')
    { 
        var new_vp := (ad: AttestationData) 
                                        => consensus_is_valid_attestation_data(
                                                process.attestation_slashing_db, 
                                                ad, 
                                                attestation_duty);                

        var slot := attestation_duty.slot;

        assert process' == process.(
                                    current_attestation_duty := Some(attestation_duty),
                                    latest_attestation_duty := Some(attestation_duty),
                                    attestation_consensus_engine_state := startConsensusInstance(
                                    process.attestation_consensus_engine_state,
                                    attestation_duty.slot,
                                    attestation_duty,
                                    process.attestation_slashing_db
                                    )
                            );

        assert process'.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys 
                    == process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys 
                            + {attestation_duty.slot};

        // lemma_inv17_f_start_next_duty(process, attestation_duty, process');

        
    } 
}