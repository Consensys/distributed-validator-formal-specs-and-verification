include "../../../../common/commons.dfy"
include "../../common/attestation_creation_instrumented.dfy"
include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_attestation_creation.dfy"
include "../inv.dfy"
include "../../../common/helper_sets_lemmas.dfy"
include "../../common/common_proofs.dfy"
include "../../common/dvc_spec_axioms.dfy"
include "invs_fnc_1.dfy"


module Fnc_Invs_2
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Helper_Sets_Lemmas
    import opened Common_Proofs
    import opened Fnc_Invs_1
    import opened DVC_Spec_Axioms
    
    
    

    lemma lemma_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)    
    requires inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(s)
    ensures inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(s')
    { }

    lemma lemma_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(process)
    ensures inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(process')
    { }

    lemma lemma_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires attestation_duty in process.all_rcvd_duties
    requires inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(process)
    ensures inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(process')
    { } 

    lemma lemma_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(process)
    ensures inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(process')
    { } 

    

    lemma lemma_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state    
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process)
    requires inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(process)
    ensures inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(process')
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

                    lemma_updateConsensusInstanceValidityCheck(
                                process.attestation_consensus_engine_state,
                                new_attestation_slashing_db,
                                process_mod.attestation_consensus_engine_state 
                                );

                    assert process_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                                == process.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
                                        + process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

                    assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process_mod);

                    assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
                    assert inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(process_mod);
                    lemma_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_f_check_for_next_queued_duty(process_mod, process');
                }
                else
                { 
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    );     
                    assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
                    assert inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(process_mod);
                    lemma_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
                }
        }
        else
        { 
            assert process'.all_rcvd_duties == process.all_rcvd_duties;
        }
    }

    

    lemma lemma_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process)
    requires inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(process)
    ensures inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(process')
    {
        
        if  && process.current_attestation_duty.isPresent()
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

            var new_attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                                                                process.attestation_consensus_engine_state,
                                                                attestation_slashing_db
                                                        );

            var process_mod := 
                process.(
                    current_attestation_duty := None,
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                    attestation_slashing_db := attestation_slashing_db,
                    attestation_consensus_engine_state := new_attestation_consensus_engine_state
                );
        
            lemma_updateConsensusInstanceValidityCheck(
                                    process.attestation_consensus_engine_state,
                                    attestation_slashing_db,
                                    process_mod.attestation_consensus_engine_state 
                                    );

            assert process_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                        == process.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
                                + process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;


            assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
            assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process_mod);

            assert inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(process_mod);

            var ret_dvc := f_check_for_next_queued_duty(process_mod).state;
            lemma_inv_queued_att_duty_is_rcvd_duty_f_check_for_next_queued_duty(process_mod, ret_dvc);
            assert inv_queued_att_duty_is_rcvd_duty_body(ret_dvc);
            
            lemma_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_f_check_for_next_queued_duty(process_mod, ret_dvc);
            assert inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(ret_dvc);

            assert process' == ret_dvc;
        }      
    }

    lemma lemma_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process)
    requires inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(process)
    ensures inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(process')
    {
        var process_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );        

        assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
        assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process_mod);
        assert inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(process_mod);
        
        lemma_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_f_check_for_next_queued_duty(process_mod, process');        
    }

    lemma lemma_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process)
    requires inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(process)
    ensures inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(process')
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
        
        assert inv_queued_att_duty_is_rcvd_duty_body(process);
        assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process);
        assert inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(process);

        if process.current_attestation_duty.isPresent() && process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            var decided_attestation_data := att_consensus_instances_already_decided[process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);
            var new_attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                                                            process.attestation_consensus_engine_state,
                                                            new_attestation_slashing_db
                                                          );  
            var process_mod := process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := new_attestation_consensus_engine_state
            );

            lemma_updateConsensusInstanceValidityCheck(
                                process.attestation_consensus_engine_state,
                                new_attestation_slashing_db,
                                process_mod.attestation_consensus_engine_state 
                                );

            assert process_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                    == process.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
                            + process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

            
            assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
            assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process_mod);
            assert inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(process_mod);

            lemma_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_f_check_for_next_queued_duty(process_mod, process');
        }
        else
        {               
            assert inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(process);
        }
    }  

    
    lemma lemma_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)    
    requires inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(s)
    ensures inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(s')
    { }

    lemma lemma_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process)
    ensures inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process')
    { }

    lemma lemma_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires attestation_duty in process.all_rcvd_duties
    requires inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process)
    ensures inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process')
    { } 

    lemma lemma_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process)
    ensures inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process')
    { } 

    lemma lemma_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state    
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    requires inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process)
    ensures inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process')
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
                    var new_attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                            process.attestation_consensus_engine_state,
                            new_attestation_slashing_db
                        ); 

                    assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body_ces(process.attestation_consensus_engine_state);
                    assert new_attestation_consensus_engine_state 
                                == updateConsensusInstanceValidityCheck(
                                        process.attestation_consensus_engine_state, 
                                        new_attestation_slashing_db);
                    
                    lemma_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_updateConsensusInstanceValidityCheck(
                        process.attestation_consensus_engine_state,
                        new_attestation_slashing_db,
                        new_attestation_consensus_engine_state);
                    assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body_ces(new_attestation_consensus_engine_state);

                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..],
                        future_att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided - {queue_head.slot},
                        attestation_slashing_db := new_attestation_slashing_db,
                        attestation_consensus_engine_state := new_attestation_consensus_engine_state                                              
                    );
                    assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process_mod);

                    lemma_updateConsensusInstanceValidityCheck(
                                process.attestation_consensus_engine_state,
                                new_attestation_slashing_db,
                                process_mod.attestation_consensus_engine_state 
                                );

                    assert process_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                                == process.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
                                        + process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;
                    assert inv_consensus_instances_only_for_rcvd_duties_body(process_mod);
                    assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);

                    lemma_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_f_check_for_next_queued_duty(process_mod, process');
                    assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process');
                }
                else
                { 
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    );     
                    assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
                    assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process_mod);
                    lemma_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
                    assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process');
                }
        }
        else
        { 
            assert process'.all_rcvd_duties == process.all_rcvd_duties;
            assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process');
        }
    }

    lemma lemma_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    requires inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process)
    ensures inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process')
    {
        
        if  && process.current_attestation_duty.isPresent()
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

            var new_attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                                                                process.attestation_consensus_engine_state,
                                                                attestation_slashing_db
                                                        );

            var process_mod := 
                process.(
                    current_attestation_duty := None,
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                    attestation_slashing_db := attestation_slashing_db,
                    attestation_consensus_engine_state := new_attestation_consensus_engine_state
                );
        
            lemma_updateConsensusInstanceValidityCheck(
                                    process.attestation_consensus_engine_state,
                                    attestation_slashing_db,
                                    process_mod.attestation_consensus_engine_state 
                                    );

            assert process_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                        == process.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
                                + process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;


            assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
            assert inv_consensus_instances_only_for_rcvd_duties_body(process_mod);

            assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process_mod);

            var ret_dvc := f_check_for_next_queued_duty(process_mod).state;
            lemma_inv_queued_att_duty_is_rcvd_duty_f_check_for_next_queued_duty(process_mod, ret_dvc);
            assert inv_queued_att_duty_is_rcvd_duty_body(ret_dvc);
            
            lemma_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_f_check_for_next_queued_duty(process_mod, ret_dvc);
            assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(ret_dvc);

            assert process' == ret_dvc;      
        }
    }

    lemma lemma_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    requires inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process)
    ensures inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process')
    {
        var process_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );        

        assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
        assert inv_consensus_instances_only_for_rcvd_duties_body(process_mod);
        assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process_mod);
        
        lemma_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_f_check_for_next_queued_duty(process_mod, process');        
    }

    lemma lemma_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    requires inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process)
    ensures inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process')
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
        
        assert inv_queued_att_duty_is_rcvd_duty_body(process);
        assert inv_consensus_instances_only_for_rcvd_duties_body(process);
        assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process);

        if process.current_attestation_duty.isPresent() && process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            var decided_attestation_data := att_consensus_instances_already_decided[process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);
            var new_attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                                                            process.attestation_consensus_engine_state,
                                                            new_attestation_slashing_db
                                                          );  
            var process_mod := process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := new_attestation_consensus_engine_state
            );

            lemma_updateConsensusInstanceValidityCheck(
                                process.attestation_consensus_engine_state,
                                new_attestation_slashing_db,
                                process_mod.attestation_consensus_engine_state 
                                );

            assert process_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                    == process.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
                            + process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

            
            assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
            assert inv_consensus_instances_only_for_rcvd_duties_body(process_mod);
            assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process_mod);

            lemma_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_f_check_for_next_queued_duty(process_mod, process');
        }
        else
        {               
            assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(process);
        }
    } 

    lemma lemma_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)    
    requires inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(s)
    ensures inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(s')
    { }

    lemma lemma_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process)
    ensures inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process')
    { }

    lemma lemma_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires attestation_duty in process.all_rcvd_duties
    requires inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process)
    ensures inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process')
    { } 

    lemma lemma_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process)
    ensures inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process')
    { } 

    lemma lemma_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state    
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process)
    requires inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process)
    ensures inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process')
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

                    lemma_updateConsensusInstanceValidityCheck(
                                process.attestation_consensus_engine_state,
                                new_attestation_slashing_db,
                                process_mod.attestation_consensus_engine_state 
                                );

                    assert process_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                                == process.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
                                        + process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

                    assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process_mod);

                    assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
                    assert inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process_mod);
                    lemma_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_f_check_for_next_queued_duty(process_mod, process');
                }
                else
                { 
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    );     
                    assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
                    assert inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process_mod);
                    lemma_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
                }
        }
        else
        { 
            assert process'.all_rcvd_duties == process.all_rcvd_duties;
        }
    }

    lemma lemma_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process)
    requires inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process)
    ensures inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process')
    {
        
        if  && process.current_attestation_duty.isPresent()
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

            var new_attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                                                                process.attestation_consensus_engine_state,
                                                                attestation_slashing_db
                                                        );

            var process_mod := 
                process.(
                    current_attestation_duty := None,
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                    attestation_slashing_db := attestation_slashing_db,
                    attestation_consensus_engine_state := new_attestation_consensus_engine_state
                );
        
            lemma_updateConsensusInstanceValidityCheck(
                                    process.attestation_consensus_engine_state,
                                    attestation_slashing_db,
                                    process_mod.attestation_consensus_engine_state 
                                    );

            assert process_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                        == process.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
                                + process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;


            assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
            assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process_mod);

            assert inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process_mod);

            var ret_dvc := f_check_for_next_queued_duty(process_mod).state;
            lemma_inv_queued_att_duty_is_rcvd_duty_f_check_for_next_queued_duty(process_mod, ret_dvc);
            assert inv_queued_att_duty_is_rcvd_duty_body(ret_dvc);
            
            lemma_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_f_check_for_next_queued_duty(process_mod, ret_dvc);
            assert inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(ret_dvc);

            assert process' == ret_dvc; 
        }       
    }

    lemma lemma_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process)
    requires inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process)
    ensures inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process')
    {
        var process_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );        

        assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
        assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process_mod);
        assert inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process_mod);
        
        lemma_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_f_check_for_next_queued_duty(process_mod, process');        
    }

    lemma lemma_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process)
    requires inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process)
    ensures inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process')
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
        
        assert inv_queued_att_duty_is_rcvd_duty_body(process);
        assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process);
        assert inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process);

        if process.current_attestation_duty.isPresent() && process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            var decided_attestation_data := att_consensus_instances_already_decided[process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);
            var new_attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                                                            process.attestation_consensus_engine_state,
                                                            new_attestation_slashing_db
                                                          );  
            var process_mod := process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := new_attestation_consensus_engine_state
            );

            lemma_updateConsensusInstanceValidityCheck(
                                process.attestation_consensus_engine_state,
                                new_attestation_slashing_db,
                                process_mod.attestation_consensus_engine_state 
                                );

            assert process_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                    == process.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
                            + process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

            
            assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
            assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process_mod);
            assert inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process_mod);

            lemma_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_f_check_for_next_queued_duty(process_mod, process');
        }
        else
        {               
            assert inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process);
        }
    }   

    lemma lemma_concl_monotonic_att_slashing_db_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)    
    ensures s.attestation_slashing_db <= s'.attestation_slashing_db
    { }

    lemma lemma_concl_monotonic_att_slashing_db_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    ensures process.attestation_slashing_db <= process'.attestation_slashing_db    
    { }

    lemma lemma_concl_monotonic_att_slashing_db_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state       
    ensures process.attestation_slashing_db <= process'.attestation_slashing_db 
    { } 

    lemma lemma_concl_monotonic_att_slashing_db_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    ensures process.attestation_slashing_db <= process'.attestation_slashing_db     
    { } 


    lemma lemma_concl_monotonic_att_slashing_db_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state        
    ensures process.attestation_slashing_db <= process'.attestation_slashing_db 
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

                    assert process.attestation_slashing_db <= process_mod.attestation_slashing_db;
                    
                    lemma_concl_monotonic_att_slashing_db_f_check_for_next_queued_duty(process_mod, process');
                }
                else
                { 
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    );     
                    assert process.attestation_slashing_db <= process_mod.attestation_slashing_db;
                    lemma_concl_monotonic_att_slashing_db_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
                }
        }
        else
        { 
            assert process.attestation_slashing_db == process'.attestation_slashing_db;
        }
    }

    lemma lemma_concl_monotonic_att_slashing_db_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    ensures process.attestation_slashing_db <= process'.attestation_slashing_db
    {
        
        if  && process.current_attestation_duty.isPresent()
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

            var new_attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                                                                process.attestation_consensus_engine_state,
                                                                attestation_slashing_db
                                                        );

            var process_mod := 
                process.(
                    current_attestation_duty := None,
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                    attestation_slashing_db := attestation_slashing_db,
                    attestation_consensus_engine_state := new_attestation_consensus_engine_state
                );
        
            assert process.attestation_slashing_db <= process_mod.attestation_slashing_db;

            var ret_dvc := f_check_for_next_queued_duty(process_mod).state;
            
            lemma_concl_monotonic_att_slashing_db_f_check_for_next_queued_duty(process_mod, ret_dvc);
            
            assert process' == ret_dvc;  
        }      
    }

    lemma lemma_concl_monotonic_att_slashing_db_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    ensures process.attestation_slashing_db <= process'.attestation_slashing_db
    {
        var process_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );        

        assert process.attestation_slashing_db <= process_mod.attestation_slashing_db;

        lemma_concl_monotonic_att_slashing_db_f_check_for_next_queued_duty(process_mod, process');        
    }

    lemma lemma_concl_monotonic_att_slashing_db_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state   
    ensures process.attestation_slashing_db <= process'.attestation_slashing_db     
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
            var new_attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                                                            process.attestation_consensus_engine_state,
                                                            new_attestation_slashing_db
                                                          );  
            var process_mod := process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := new_attestation_consensus_engine_state
            );

            

            lemma_concl_monotonic_att_slashing_db_f_check_for_next_queued_duty(process_mod, process');
        }
        else
        { }
    } 

    lemma lemma_concl_monotonic_att_slashing_db_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    ) 
    requires NextEvent.requires(dv, event, dv')    
    requires NextEvent(dv, event, dv')  
    ensures concl_monotonic_att_slashing_db(dv, event, dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        lemma_concl_monotonic_att_slashing_db_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_concl_monotonic_att_slashing_db_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lemma_concl_monotonic_att_slashing_db_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lemma_concl_monotonic_att_slashing_db_add_block_to_bn(dvc, block, dvc_mod);
                        lemma_concl_monotonic_att_slashing_db_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }

    lemma lemma_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)    
    requires inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(s)
    ensures inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(s')
    { }

    lemma lemma_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process)
    ensures inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process')
    { }

    lemma lemma_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires attestation_duty in process.all_rcvd_duties
    requires inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process)
    ensures inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process')
    { } 

    lemma lemma_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process)
    ensures inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process')
    { } 

    

    lemma lemma_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state    
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)    
    requires inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process)
    ensures inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process')
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
                    assert process.attestation_slashing_db <= new_attestation_slashing_db;
                    assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(process.attestation_consensus_engine_state, 
                                          process.attestation_slashing_db);        


                    forall s: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation> |
                            ( && s  in process.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                              && vp in process.attestation_consensus_engine_state.att_slashing_db_hist[s]
                              && db in process.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
                            )  
                    ensures db <= new_attestation_slashing_db               
                    {
                        calc {
                            db; 
                            <=
                            process.attestation_slashing_db;
                            <=
                            new_attestation_slashing_db;
                        }                        
                    }

                    assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(process.attestation_consensus_engine_state, 
                                          new_attestation_slashing_db);

                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..],
                        future_att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided - {queue_head.slot},
                        attestation_slashing_db := new_attestation_slashing_db,
                        attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                            process.attestation_consensus_engine_state,
                            new_attestation_slashing_db
                        )                        
                    );
                    assert process_mod.attestation_slashing_db <= new_attestation_slashing_db;                    
                    assert inv_consensus_instances_only_for_rcvd_duties_body(process_mod);
                    assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(process_mod.attestation_consensus_engine_state, 
                                          new_attestation_slashing_db);

                    assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);                    
                    assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process_mod);
                    lemma_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_f_check_for_next_queued_duty(process_mod, process');
                }
                else
                { 
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    );     
                    assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
                    assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process_mod);
                    lemma_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
                }
        }
        else
        { 
            assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process');
        }
    }

    lemma lemma_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    requires inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process)
    ensures inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process')
    {
        
        if  && process.current_attestation_duty.isPresent()
            && id == process.current_attestation_duty.safe_get().slot
        {
            var local_current_attestation_duty := process.current_attestation_duty.safe_get();
            var attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);
            assert process.attestation_slashing_db <= attestation_slashing_db;
            assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(process.attestation_consensus_engine_state, 
                                process.attestation_slashing_db); 

            forall s: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation> |
                                ( && s  in process.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                                && vp in process.attestation_consensus_engine_state.att_slashing_db_hist[s]
                                && db in process.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
                                )   
            ensures db <= attestation_slashing_db               
            {
                calc {
                    db; 
                    <=
                    process.attestation_slashing_db;
                    <=
                    attestation_slashing_db;
                }                        
            }

            assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(process.attestation_consensus_engine_state, 
                                attestation_slashing_db);

            var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
            var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
            var attestation_signature_share := rs_sign_attestation(decided_attestation_data, fork_version, attestation_signing_root, process.rs);
            var attestation_with_signature_share := AttestationShare(
                    aggregation_bits := get_aggregation_bits(local_current_attestation_duty.validator_index),
                    data := decided_attestation_data, 
                    signature := attestation_signature_share
                ); 

            var new_attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                                                                process.attestation_consensus_engine_state,
                                                                attestation_slashing_db
                                                        );

            assert inv_consensus_instances_only_for_rcvd_duties_body(process);


            lemma_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_updateConsensusInstanceValidityCheck(
                                    process.attestation_consensus_engine_state,
                                    attestation_slashing_db,
                                    new_attestation_consensus_engine_state
                                    );


            assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(new_attestation_consensus_engine_state, attestation_slashing_db);

            var process_mod := 
                process.(
                    current_attestation_duty := None,
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                    attestation_slashing_db := attestation_slashing_db,
                    attestation_consensus_engine_state := new_attestation_consensus_engine_state
                );

            assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process_mod);
        
            var ret_dvc := f_check_for_next_queued_duty(process_mod).state;
            lemma_inv_queued_att_duty_is_rcvd_duty_f_check_for_next_queued_duty(process_mod, ret_dvc);
            assert inv_queued_att_duty_is_rcvd_duty_body(ret_dvc);
            
            
            lemma_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_f_check_for_next_queued_duty(process_mod, ret_dvc);
            assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(ret_dvc);

            assert process' == ret_dvc;   
        }     
    }

    lemma lemma_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    requires inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process)
    ensures inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process')
    {
        var process_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );        

        assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
        assert inv_consensus_instances_only_for_rcvd_duties_body(process_mod);
        assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process_mod);
        
        lemma_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_f_check_for_next_queued_duty(process_mod, process');        
    }

    lemma lemma_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    requires inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process)
    ensures inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process')
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
        
        assert inv_queued_att_duty_is_rcvd_duty_body(process);
        assert inv_consensus_instances_only_for_rcvd_duties_body(process);
        assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process);

        if process.current_attestation_duty.isPresent() && process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            var decided_attestation_data := att_consensus_instances_already_decided[process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);

            assert process.attestation_slashing_db <= new_attestation_slashing_db;
            assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(process.attestation_consensus_engine_state, 
                              process.attestation_slashing_db); 

            forall s: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation> |
                            ( && s  in process.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                              && vp in process.attestation_consensus_engine_state.att_slashing_db_hist[s]
                              && db in process.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
                            )   
            ensures db <= new_attestation_slashing_db               
            {
                calc {
                    db; 
                    <=
                    process.attestation_slashing_db;
                    <=
                    new_attestation_slashing_db;
                }                        
            }

            assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(process.attestation_consensus_engine_state, 
                              new_attestation_slashing_db);

            var new_attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                                                            process.attestation_consensus_engine_state,
                                                            new_attestation_slashing_db
                                                          );  
            var process_mod := process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := new_attestation_consensus_engine_state
            );

            lemma_updateConsensusInstanceValidityCheck(
                                process.attestation_consensus_engine_state,
                                new_attestation_slashing_db,
                                process_mod.attestation_consensus_engine_state 
                                );

            assert process_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                    == process.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
                            + process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

            
            assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
            assert inv_consensus_instances_only_for_rcvd_duties_body(process_mod);
            assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process_mod);

            lemma_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_f_check_for_next_queued_duty(process_mod, process');
        }
        else
        {               
            assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(process);
        }
    }   
    
    lemma lemma_concl_monotonic_att_slashing_db_hist_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)    
    ensures concl_monotonic_att_slashing_db_hist_body(s, s')
    { }

    lemma lemma_concl_monotonic_att_slashing_db_hist_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    ensures concl_monotonic_att_slashing_db_hist_body(process, process')
    { }

    lemma lemma_concl_monotonic_att_slashing_db_hist_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state       
    ensures concl_monotonic_att_slashing_db_hist_body(process, process')
    { } 

    lemma lemma_concl_monotonic_att_slashing_db_hist_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    ensures concl_monotonic_att_slashing_db_hist_body(process, process')     
    { } 


    lemma lemma_concl_monotonic_att_slashing_db_hist_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state        
    ensures concl_monotonic_att_slashing_db_hist_body(process, process')
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

                    assert process.attestation_slashing_db <= process_mod.attestation_slashing_db;
                    
                    lemma_concl_monotonic_att_slashing_db_hist_f_check_for_next_queued_duty(process_mod, process');
                }
                else
                { 
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    );     
                    assert process.attestation_slashing_db <= process_mod.attestation_slashing_db;
                    lemma_concl_monotonic_att_slashing_db_hist_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
                }
        }
        else
        { 
            assert process.attestation_slashing_db == process'.attestation_slashing_db;
        }
    }

    lemma lemma_concl_monotonic_att_slashing_db_hist_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    ensures concl_monotonic_att_slashing_db_hist_body(process, process')
    {
        
        if  && process.current_attestation_duty.isPresent()
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

            var new_attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                                                                process.attestation_consensus_engine_state,
                                                                attestation_slashing_db
                                                        );

            var process_mod := 
                process.(
                    current_attestation_duty := None,
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                    attestation_slashing_db := attestation_slashing_db,
                    attestation_consensus_engine_state := new_attestation_consensus_engine_state
                );
        
            assert process.attestation_slashing_db <= process_mod.attestation_slashing_db;

            var ret_dvc := f_check_for_next_queued_duty(process_mod).state;
            
            lemma_concl_monotonic_att_slashing_db_hist_f_check_for_next_queued_duty(process_mod, ret_dvc);
            
            assert process' == ret_dvc;       
        } 
    }

    lemma lemma_concl_monotonic_att_slashing_db_hist_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    ensures concl_monotonic_att_slashing_db_hist_body(process, process')
    {
        var process_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );        

        assert process.attestation_slashing_db <= process_mod.attestation_slashing_db;

        lemma_concl_monotonic_att_slashing_db_hist_f_check_for_next_queued_duty(process_mod, process');        
    }

    lemma lemma_concl_monotonic_att_slashing_db_hist_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state   
    ensures concl_monotonic_att_slashing_db_hist_body(process, process')    
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
            var new_attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                                                            process.attestation_consensus_engine_state,
                                                            new_attestation_slashing_db
                                                          );  
            var process_mod := process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := new_attestation_consensus_engine_state
            );

            

            lemma_concl_monotonic_att_slashing_db_hist_f_check_for_next_queued_duty(process_mod, process');
        }
        else
        { }
    } 

    lemma lemma_inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)    
    requires inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_body(s)
    ensures inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_body(s')
    { }

    lemma lemma_inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_body(process)
    ensures inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_body(process')   
    { }

    lemma lemma_inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state       
    requires inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_body(process)
    ensures inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_body(process')   
    { } 

    lemma lemma_inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_body(process)
    ensures inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_body(process')     
    { } 


    lemma lemma_inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state        
    requires inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_body(process)
    ensures inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_body(process')   
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

                    assert process.attestation_slashing_db <= process_mod.attestation_slashing_db;
                    
                    lemma_inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_f_check_for_next_queued_duty(process_mod, process');
                }
                else
                { 
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    );     
                    assert process.attestation_slashing_db <= process_mod.attestation_slashing_db;
                    lemma_inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
                }
        }
        else
        { 
            assert process.attestation_slashing_db == process'.attestation_slashing_db;
        }
    }

    lemma lemma_inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_body(process)
    ensures inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_body(process')   
    {
        
        if  && process.current_attestation_duty.isPresent()
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

            var new_attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                                                                process.attestation_consensus_engine_state,
                                                                attestation_slashing_db
                                                        );

            var process_mod := 
                process.(
                    current_attestation_duty := None,
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                    attestation_slashing_db := attestation_slashing_db,
                    attestation_consensus_engine_state := new_attestation_consensus_engine_state
                );
        
            assert process.attestation_slashing_db <= process_mod.attestation_slashing_db;

            var ret_dvc := f_check_for_next_queued_duty(process_mod).state;
            
            lemma_inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_f_check_for_next_queued_duty(process_mod, ret_dvc);
            
            assert process' == ret_dvc;      
        }  
    }

    lemma lemma_inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_body(process)
    ensures inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_body(process')   
    {
        var process_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );        

        assert process.attestation_slashing_db <= process_mod.attestation_slashing_db;

        lemma_inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_f_check_for_next_queued_duty(process_mod, process');        
    }

    lemma lemma_inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state   
    requires inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_body(process)
    ensures inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_body(process')    
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
            var new_attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                                                            process.attestation_consensus_engine_state,
                                                            new_attestation_slashing_db
                                                          );  
            var process_mod := process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := new_attestation_consensus_engine_state
            );

            

            lemma_inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_f_check_for_next_queued_duty(process_mod, process');
        }
        else
        { }
    } 

    lemma lemma_inv_rcvd_attn_shares_are_from_sent_messages_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)    
    ensures s'.rcvd_attestation_shares == s.rcvd_attestation_shares 
    { }

    /*
    lemma lemma_inv_rcvd_attn_shares_are_from_sent_messages_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state     
    
    ensures && var k := (attestation_share.data, attestation_share.aggregation_bits);
            && ( forall i, j 
                    | 
                        && i in process'.rcvd_attestation_shares 
                        && j in process'.rcvd_attestation_shares[i]
                    :: 
                        && ( (  || i != attestation_share.data.slot
                                || j != k
                             )
                             ==> 
                             process'.rcvd_attestation_shares[i][j] <= process.rcvd_attestation_shares[i][j]
                           )
                        && ( ( && i == attestation_share.data.slot
                               && j == k
                               && ( || i !in process.rcvd_attestation_shares 
                                    || j !in process.rcvd_attestation_shares[i]
                                  )       
                             )
                             ==> 
                             process'.rcvd_attestation_shares[i][j] <= {attestation_share} 
                           )
                        && ( ( && i == attestation_share.data.slot
                               && j == k
                               && i in process.rcvd_attestation_shares 
                               && j in process.rcvd_attestation_shares[i]                                 
                             )
                             ==> 
                                process'.rcvd_attestation_shares[i][j] 
                                <= process.rcvd_attestation_shares[i][j] + {attestation_share} 
                           )
                   )                   
                   
    { 
        var activate_att_consensus_intances := process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

        if 
            || (activate_att_consensus_intances == {} && !process.latest_attestation_duty.isPresent())
            || (activate_att_consensus_intances != {} && minInSet(activate_att_consensus_intances) <= attestation_share.data.slot)
            || (activate_att_consensus_intances == {} && process.current_attestation_duty.isPresent() && process.current_attestation_duty.safe_get().slot <= attestation_share.data.slot)                
            || (activate_att_consensus_intances == {} && !process.current_attestation_duty.isPresent() && process.latest_attestation_duty.isPresent() && process.latest_attestation_duty.safe_get().slot < attestation_share.data.slot)
        {
            var k := (attestation_share.data, attestation_share.aggregation_bits);
            var attestation_shares_db_at_slot := getOrDefault(process.rcvd_attestation_shares, attestation_share.data.slot, map[]);

            assert && ( attestation_share.data.slot in process.rcvd_attestation_shares.Keys
                        ==> 
                        attestation_shares_db_at_slot == process.rcvd_attestation_shares[attestation_share.data.slot]
                      )
                   && ( attestation_share.data.slot !in process.rcvd_attestation_shares.Keys
                        ==> 
                        attestation_shares_db_at_slot == map[]
                      );

            var new_set := getOrDefault(attestation_shares_db_at_slot, k, {}) + 
                                                {attestation_share};

            assert && (k in attestation_shares_db_at_slot.Keys 
                            ==> new_set == attestation_shares_db_at_slot[k] + {attestation_share}
                      )
                   && (k !in attestation_shares_db_at_slot.Keys 
                            ==> new_set == {attestation_share}
                      );
                
            var new_attestation_shares_db := 
                        process.rcvd_attestation_shares[
                            attestation_share.data.slot := 
                                attestation_shares_db_at_slot[
                                            k := new_set                                                
                                            ]
                                ];

            assert attestation_share.data.slot in new_attestation_shares_db.Keys;
            assert k in new_attestation_shares_db[attestation_share.data.slot].Keys;

            assert ( forall i, j 
                    | 
                        && i in new_attestation_shares_db
                        && j in new_attestation_shares_db[i]
                    :: 
                        && ( (  || i != attestation_share.data.slot
                                || j != k
                             )
                             ==> 
                             new_attestation_shares_db[i][j] == process.rcvd_attestation_shares[i][j]
                           )
                        && ( ( && i == attestation_share.data.slot
                               && j == k
                               && ( || i !in process.rcvd_attestation_shares 
                                    || j !in process.rcvd_attestation_shares[i]
                                  )       
                             )
                             ==> 
                             new_attestation_shares_db[i][j] == {attestation_share} 
                           )
                        && ( ( && i == attestation_share.data.slot
                               && j == k
                               && i in process.rcvd_attestation_shares 
                               && j in process.rcvd_attestation_shares[i]                                 
                             )
                             ==> 
                                new_attestation_shares_db[i][j] 
                                == process.rcvd_attestation_shares[i][j] + {attestation_share} 
                           )
                   )
            ;

            var process_mod := process.(
                    rcvd_attestation_shares := new_attestation_shares_db
                );

            assert ( forall i, j 
                    | 
                        && i in process_mod.rcvd_attestation_shares 
                        && j in process_mod.rcvd_attestation_shares[i]
                    :: 
                        && ( (  || i != attestation_share.data.slot
                                || j != k
                             )
                             ==> 
                             process_mod.rcvd_attestation_shares[i][j] == process.rcvd_attestation_shares[i][j]
                           )
                        && ( ( && i == attestation_share.data.slot
                               && j == k
                               && ( || i !in process.rcvd_attestation_shares 
                                    || j !in process.rcvd_attestation_shares[i]
                                  )       
                             )
                             ==> 
                             process_mod.rcvd_attestation_shares[i][j] == {attestation_share} 
                           )
                        && ( ( && i == attestation_share.data.slot
                               && j == k
                               && i in process.rcvd_attestation_shares 
                               && j in process.rcvd_attestation_shares[i]                                 
                             )
                             ==> 
                                process_mod.rcvd_attestation_shares[i][j] 
                                == process.rcvd_attestation_shares[i][j] + {attestation_share} 
                           )
                   )
            ;

            if process_mod.construct_signed_attestation_signature(process_mod.rcvd_attestation_shares[attestation_share.data.slot][k]).isPresent()
            {
                assert process'.rcvd_attestation_shares == process_mod.rcvd_attestation_shares;            
            }
            else
            {
                assert process'.rcvd_attestation_shares == process_mod.rcvd_attestation_shares;            
            } 
                               
        }
        else
        {             
            assert process'.rcvd_attestation_shares == process.rcvd_attestation_shares;            
        }
    }
    */

    lemma lemma_inv_rcvd_attn_shares_are_from_sent_messages_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state       
    ensures process'.rcvd_attestation_shares == process.rcvd_attestation_shares
    { } 

    lemma lemma_inv_rcvd_attn_shares_are_from_sent_messages_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    ensures process'.rcvd_attestation_shares == process.rcvd_attestation_shares
    { } 


    lemma lemma_inv_rcvd_attn_shares_are_from_sent_messages_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state        
    ensures process'.rcvd_attestation_shares == process.rcvd_attestation_shares
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

                    assert process.attestation_slashing_db <= process_mod.attestation_slashing_db;
                    
                    lemma_inv_rcvd_attn_shares_are_from_sent_messages_f_check_for_next_queued_duty(process_mod, process');
                }
                else
                { 
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    );     
                    assert process.attestation_slashing_db <= process_mod.attestation_slashing_db;
                    lemma_inv_rcvd_attn_shares_are_from_sent_messages_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
                }
        }
        else
        { 
            assert process.attestation_slashing_db == process'.attestation_slashing_db;
        }
    }

    lemma lemma_inv_rcvd_attn_shares_are_from_sent_messages_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    ensures process'.rcvd_attestation_shares == process.rcvd_attestation_shares
    {
        
        if  && process.current_attestation_duty.isPresent()
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

            var new_attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                                                                process.attestation_consensus_engine_state,
                                                                attestation_slashing_db
                                                        );

            var process_mod := 
                process.(
                    current_attestation_duty := None,
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                    attestation_slashing_db := attestation_slashing_db,
                    attestation_consensus_engine_state := new_attestation_consensus_engine_state
                );
        
            assert process.attestation_slashing_db <= process_mod.attestation_slashing_db;

            var ret_dvc := f_check_for_next_queued_duty(process_mod).state;
            
            lemma_inv_rcvd_attn_shares_are_from_sent_messages_f_check_for_next_queued_duty(process_mod, ret_dvc);
            
            assert process' == ret_dvc;      
        } 
    }

    lemma lemma_inv_rcvd_attn_shares_are_from_sent_messages_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    ensures process'.rcvd_attestation_shares == process.rcvd_attestation_shares
    {
        var process_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );        

        assert process.attestation_slashing_db <= process_mod.attestation_slashing_db;

        lemma_inv_rcvd_attn_shares_are_from_sent_messages_f_check_for_next_queued_duty(process_mod, process');        
    }


    lemma lemma_inv_rcvd_attn_shares_are_from_sent_messages_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state   
    ensures process'.rcvd_attestation_shares.Keys <= process.rcvd_attestation_shares.Keys
    ensures ( forall i, j 
                    | 
                        && i in process'.rcvd_attestation_shares 
                        && j in process'.rcvd_attestation_shares[i]
                    :: 
                        (
                        && i in process.rcvd_attestation_shares 
                        && j in process.rcvd_attestation_shares[i]
                        && ( process'.rcvd_attestation_shares[i][j] 
                             <= 
                             process.rcvd_attestation_shares[i][j] 
                           )
                        )
            )  
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
            var new_attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                                                            process.attestation_consensus_engine_state,
                                                            new_attestation_slashing_db
                                                          );  
            var process_mod := process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := new_attestation_consensus_engine_state
            );

            

            lemma_inv_rcvd_attn_shares_are_from_sent_messages_f_check_for_next_queued_duty(process_mod, process');
        }
        else
        { }
    } 

    lemma lemma_multicast_getMessagesFromMessagesWithRecipient(dvc: DVCState, attestation_with_signature_share: AttestationShare)
    requires |dvc.peers| > 0    
    ensures getMessagesFromMessagesWithRecipient(multicast(attestation_with_signature_share, dvc.peers))
            ==
            { attestation_with_signature_share }            
    {
        var mcast_msgs := multicast(attestation_with_signature_share, dvc.peers);
        assert (forall msg | msg in mcast_msgs :: msg.message == attestation_with_signature_share);
        assert |mcast_msgs| > 0;
        
        var msgs_content := getMessagesFromMessagesWithRecipient(mcast_msgs);
        

        var all_mcast_msgs := mcast_msgs;
        var checked_mcast_msgs := {};

        while all_mcast_msgs != {}            
            invariant all_mcast_msgs + checked_mcast_msgs == mcast_msgs
            invariant checked_mcast_msgs == {}
                        ==> getMessagesFromMessagesWithRecipient(checked_mcast_msgs) == {}
            invariant checked_mcast_msgs != {}
                        ==> getMessagesFromMessagesWithRecipient(checked_mcast_msgs) == { attestation_with_signature_share } 
            decreases |all_mcast_msgs|
        {
            var msg :|  msg in all_mcast_msgs;
            assert msg.message ==  attestation_with_signature_share;
            all_mcast_msgs := all_mcast_msgs - {msg};
            checked_mcast_msgs := checked_mcast_msgs + {msg};
        }        

        assert getMessagesFromMessagesWithRecipient(mcast_msgs) == { attestation_with_signature_share };
    }

    lemma lemma_inv_attestation_shares_to_broadcast_are_sent_messages_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState 
    )
    requires add_block_to_bn.requires(process, block)
    requires process' == add_block_to_bn(process, block)    
    ensures process'.attestation_shares_to_broadcast == process.attestation_shares_to_broadcast
    { }

    lemma lemma_inv_attestation_shares_to_broadcast_are_sent_messages_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state       
    ensures process'.attestation_shares_to_broadcast == process.attestation_shares_to_broadcast        
    ensures process'.peers == process.peers          
    { }

    lemma lemma_inv_attestation_shares_to_broadcast_are_sent_messages_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state       
    ensures process'.attestation_shares_to_broadcast == process.attestation_shares_to_broadcast                  
    ensures process'.peers == process.peers
    { } 

    lemma lemma_inv_attestation_shares_to_broadcast_are_sent_messages_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    ensures process'.attestation_shares_to_broadcast == process.attestation_shares_to_broadcast                  
    ensures process'.peers == process.peers
    { } 

    lemma lemma_inv_attestation_shares_to_broadcast_are_sent_messages_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state        
    ensures process'.attestation_shares_to_broadcast == process.attestation_shares_to_broadcast                  
    ensures process'.peers == process.peers
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

                    assert process.attestation_slashing_db <= process_mod.attestation_slashing_db;
                    
                    lemma_inv_attestation_shares_to_broadcast_are_sent_messages_f_check_for_next_queued_duty(process_mod, process');
                }
                else
                { 
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    );     
                    assert process.attestation_slashing_db <= process_mod.attestation_slashing_db;
                    lemma_inv_attestation_shares_to_broadcast_are_sent_messages_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
                }
        }
        else
        { }
    }

    lemma lemma_inv_attestation_shares_to_broadcast_are_sent_messages_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState,
        outputs: Outputs
    )
    requires |process.peers| > 0
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires outputs == f_att_consensus_decided(process, id, decided_attestation_data).outputs    
    requires decided_attestation_data.slot == id  
    ensures (process'.attestation_shares_to_broadcast.Values - process.attestation_shares_to_broadcast.Values) <= getMessagesFromMessagesWithRecipient(outputs.att_shares_sent);
    {   
        if  && process.current_attestation_duty.isPresent()
            && id == process.current_attestation_duty.safe_get().slot
        {
            var local_current_attestation_duty := process.current_attestation_duty.safe_get();
            assert local_current_attestation_duty.slot == decided_attestation_data.slot;

            var attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);

            var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
            var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
            var attestation_signature_share := rs_sign_attestation(decided_attestation_data, fork_version, attestation_signing_root, process.rs);
            var attestation_with_signature_share := AttestationShare(
                    aggregation_bits := get_aggregation_bits(local_current_attestation_duty.validator_index),
                    data := decided_attestation_data, 
                    signature := attestation_signature_share
                ); 

            var new_attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                                                                process.attestation_consensus_engine_state,
                                                                attestation_slashing_db
                                                        );

            var process_mod := 
                process.(
                    current_attestation_duty := None,
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                    attestation_slashing_db := attestation_slashing_db,
                    attestation_consensus_engine_state := new_attestation_consensus_engine_state
                );

            var new_dvc := f_check_for_next_queued_duty(process_mod).state;
            lemma_inv_attestation_shares_to_broadcast_are_sent_messages_f_check_for_next_queued_duty(process_mod, new_dvc);        
            assert new_dvc.attestation_shares_to_broadcast == process_mod.attestation_shares_to_broadcast;
            assert new_dvc.peers == process_mod.peers;
            
            var ret_dvc_outputs := DVCStateAndOuputs(
                                        state := new_dvc,
                                        outputs := getEmptyOuputs().(
                                            att_shares_sent := multicast(attestation_with_signature_share, new_dvc.peers)
                                        )          
                                    );
            
            assert && process' == ret_dvc_outputs.state
                && decided_attestation_data.slot in process'.attestation_shares_to_broadcast.Keys
                && outputs == ret_dvc_outputs.outputs
                ;     

            lemma_multicast_getMessagesFromMessagesWithRecipient(ret_dvc_outputs.state, attestation_with_signature_share);

            assert (process'.attestation_shares_to_broadcast.Values - process.attestation_shares_to_broadcast.Values) <= getMessagesFromMessagesWithRecipient(outputs.att_shares_sent);
        }
    }

    lemma lemma_inv_attestation_shares_to_broadcast_are_sent_messages_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    ensures process'.attestation_shares_to_broadcast == process.attestation_shares_to_broadcast
    {
        var process_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );        


        lemma_inv_attestation_shares_to_broadcast_are_sent_messages_f_check_for_next_queued_duty(process_mod, process');        
    }

    lemma lemma_inv_attestation_shares_to_broadcast_are_sent_messages_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state   
    ensures process'.attestation_shares_to_broadcast.Values <= process.attestation_shares_to_broadcast.Values
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
            var new_attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                                                            process.attestation_consensus_engine_state,
                                                            new_attestation_slashing_db
                                                          );  
            var process_mod := process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := new_attestation_consensus_engine_state
            );

            

            lemma_inv_attestation_shares_to_broadcast_are_sent_messages_f_check_for_next_queued_duty(process_mod, process');
        }
        else
        { }
    } 

    lemma lemma_inv_rcvd_attn_shares_are_from_sent_messages_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state         
    ensures && var k := (attestation_share.data, attestation_share.aggregation_bits);
            && ( forall i, j 
                    | 
                        && i in process'.rcvd_attestation_shares.Keys
                        && j in process'.rcvd_attestation_shares[i].Keys
                    :: 
                        && ( (  || i != attestation_share.data.slot
                                || j != k
                             )
                             ==> 
                             process'.rcvd_attestation_shares[i][j] <= process.rcvd_attestation_shares[i][j]
                           )
                        && ( ( && i == attestation_share.data.slot
                               && j == k
                               && ( || i !in process.rcvd_attestation_shares.Keys 
                                    || j !in process.rcvd_attestation_shares[i].Keys
                                  )       
                             )
                             ==> 
                             process'.rcvd_attestation_shares[i][j] <= {attestation_share} 
                           )
                        && ( ( && i == attestation_share.data.slot
                               && j == k
                               && i in process.rcvd_attestation_shares.Keys 
                               && j in process.rcvd_attestation_shares[i].Keys                                 
                             )
                             ==> 
                                process'.rcvd_attestation_shares[i][j] 
                                <= process.rcvd_attestation_shares[i][j] + {attestation_share} 
                           )
                   )                                      
    { 
        var activate_att_consensus_intances := process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

        if 
            || (activate_att_consensus_intances == {} && !process.latest_attestation_duty.isPresent())
            || (activate_att_consensus_intances != {} && minInSet(activate_att_consensus_intances) <= attestation_share.data.slot)
            || (activate_att_consensus_intances == {} && process.current_attestation_duty.isPresent() && process.current_attestation_duty.safe_get().slot <= attestation_share.data.slot)                
            || (activate_att_consensus_intances == {} && !process.current_attestation_duty.isPresent() && process.latest_attestation_duty.isPresent() && process.latest_attestation_duty.safe_get().slot < attestation_share.data.slot)
        {
            var k := (attestation_share.data, attestation_share.aggregation_bits);
            var attestation_shares_db_at_slot := getOrDefault(process.rcvd_attestation_shares, attestation_share.data.slot, map[]);

            assert && ( attestation_share.data.slot in process.rcvd_attestation_shares.Keys
                        ==> 
                        attestation_shares_db_at_slot == process.rcvd_attestation_shares[attestation_share.data.slot]
                      )
                   && ( attestation_share.data.slot !in process.rcvd_attestation_shares.Keys
                        ==> 
                        attestation_shares_db_at_slot == map[]
                      );

            var new_set := getOrDefault(attestation_shares_db_at_slot, k, {}) + 
                                                {attestation_share};

            assert && (k in attestation_shares_db_at_slot.Keys 
                            ==> new_set == attestation_shares_db_at_slot[k] + {attestation_share}
                      )
                   && (k !in attestation_shares_db_at_slot.Keys 
                            ==> new_set == {attestation_share}
                      );
                
            var new_attestation_shares_db := 
                        process.rcvd_attestation_shares[
                            attestation_share.data.slot := 
                                attestation_shares_db_at_slot[
                                            k := new_set                                                
                                            ]
                                ];

            assert attestation_share.data.slot in new_attestation_shares_db.Keys;
            assert k in new_attestation_shares_db[attestation_share.data.slot].Keys;

            assert ( forall i, j 
                    | 
                        && i in new_attestation_shares_db.Keys
                        && j in new_attestation_shares_db[i].Keys
                    :: 
                        && ( (  || i != attestation_share.data.slot
                                || j != k
                             )
                             ==> 
                             new_attestation_shares_db[i][j] == process.rcvd_attestation_shares[i][j]
                           )
                        && ( ( && i == attestation_share.data.slot
                               && j == k
                               && ( || i !in process.rcvd_attestation_shares.Keys 
                                    || j !in process.rcvd_attestation_shares[i].Keys
                                  )       
                             )
                             ==> 
                             new_attestation_shares_db[i][j] == {attestation_share} 
                           )
                        && ( ( && i == attestation_share.data.slot
                               && j == k
                               && i in process.rcvd_attestation_shares.Keys 
                               && j in process.rcvd_attestation_shares[i].Keys                                 
                             )
                             ==> 
                                new_attestation_shares_db[i][j] 
                                == process.rcvd_attestation_shares[i][j] + {attestation_share} 
                           )
                   )
            ;


            var process_mod := process.(
                    rcvd_attestation_shares := new_attestation_shares_db
                );

            assert ( forall i, j 
                    | 
                        && i in process_mod.rcvd_attestation_shares.Keys
                        && j in process_mod.rcvd_attestation_shares[i].Keys
                    :: 
                        && ( (  || i != attestation_share.data.slot
                                || j != k
                             )
                             ==> 
                             process_mod.rcvd_attestation_shares[i][j] == process.rcvd_attestation_shares[i][j]
                           )
                        && ( ( && i == attestation_share.data.slot
                               && j == k
                               && ( || i !in process.rcvd_attestation_shares.Keys 
                                    || j !in process.rcvd_attestation_shares[i].Keys
                                  )       
                             )
                             ==> 
                             process_mod.rcvd_attestation_shares[i][j] == {attestation_share} 
                           )
                        && ( ( && i == attestation_share.data.slot
                               && j == k
                               && i in process.rcvd_attestation_shares.Keys
                               && j in process.rcvd_attestation_shares[i].Keys                                 
                             )
                             ==> 
                                process_mod.rcvd_attestation_shares[i][j] 
                                == process.rcvd_attestation_shares[i][j] + {attestation_share} 
                           )
                   )
            ;

            if process_mod.construct_signed_attestation_signature(process_mod.rcvd_attestation_shares[attestation_share.data.slot][k]).isPresent()
            {
                assert process'.rcvd_attestation_shares == process_mod.rcvd_attestation_shares;            
            }
            else
            {
                assert process'.rcvd_attestation_shares == process_mod.rcvd_attestation_shares;            
            }             
        }
        else
        {             
            assert process'.rcvd_attestation_shares == process.rcvd_attestation_shares;            
        }
    }

    
    lemma lemma_inv_rcvd_attn_shares_are_from_sent_messages_f_listen_for_attestation_shares_domain(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state         
    ensures && var k := (attestation_share.data, attestation_share.aggregation_bits);
            && var slot := attestation_share.data.slot;
            && ( forall i, j 
                    | 
                        || i != slot
                        || j != k                    
                    :: 
                        ( && i in process'.rcvd_attestation_shares.Keys
                          && j in process'.rcvd_attestation_shares[i].Keys               
                        )
                        ==>
                        ( && i in process.rcvd_attestation_shares.Keys
                          && j in process.rcvd_attestation_shares[i].Keys               
                        )
            )
    { 
        var activate_att_consensus_intances := process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

        if 
            || (activate_att_consensus_intances == {} && !process.latest_attestation_duty.isPresent())
            || (activate_att_consensus_intances != {} && minInSet(activate_att_consensus_intances) <= attestation_share.data.slot)
            || (activate_att_consensus_intances == {} && process.current_attestation_duty.isPresent() && process.current_attestation_duty.safe_get().slot <= attestation_share.data.slot)                
            || (activate_att_consensus_intances == {} && !process.current_attestation_duty.isPresent() && process.latest_attestation_duty.isPresent() && process.latest_attestation_duty.safe_get().slot < attestation_share.data.slot)
        {
            var k := (attestation_share.data, attestation_share.aggregation_bits);
            var attestation_shares_db_at_slot := getOrDefault(process.rcvd_attestation_shares, attestation_share.data.slot, map[]);
            var slot := attestation_share.data.slot;

            assert && ( attestation_share.data.slot in process.rcvd_attestation_shares.Keys
                        ==> 
                        attestation_shares_db_at_slot == process.rcvd_attestation_shares[attestation_share.data.slot]
                      )
                   && ( attestation_share.data.slot !in process.rcvd_attestation_shares.Keys
                        ==> 
                        attestation_shares_db_at_slot == map[]
                      );

            var new_set := getOrDefault(attestation_shares_db_at_slot, k, {}) + 
                                                {attestation_share};

            assert && (k in attestation_shares_db_at_slot.Keys 
                            ==> new_set == attestation_shares_db_at_slot[k] + {attestation_share}
                      )
                   && (k !in attestation_shares_db_at_slot.Keys 
                            ==> new_set == {attestation_share}
                      );
                
            var new_attestation_shares_db := 
                        process.rcvd_attestation_shares[
                            attestation_share.data.slot := 
                                attestation_shares_db_at_slot[
                                            k := new_set                                                
                                            ]
                                ];

            assert attestation_share.data.slot in new_attestation_shares_db.Keys;
            assert k in new_attestation_shares_db[attestation_share.data.slot].Keys;

            assert ( forall i, j 
                    | 
                        || i != slot
                        || j != k                    
                    :: 
                        ( && i in new_attestation_shares_db.Keys
                          && j in new_attestation_shares_db[i].Keys               
                        )
                        ==>
                        ( && i in process.rcvd_attestation_shares.Keys
                          && j in process.rcvd_attestation_shares[i].Keys               
                        )
                    )
            ;


            var process_mod := process.(
                    rcvd_attestation_shares := new_attestation_shares_db
                );

            assert ( forall i, j 
                    | 
                        || i != slot
                        || j != k                    
                    :: 
                        ( && i in process_mod.rcvd_attestation_shares.Keys
                          && j in process_mod.rcvd_attestation_shares[i].Keys               
                        )
                        ==>
                        ( && i in process.rcvd_attestation_shares.Keys
                          && j in process.rcvd_attestation_shares[i].Keys               
                        )
                    )
            ;

            if process_mod.construct_signed_attestation_signature(process_mod.rcvd_attestation_shares[attestation_share.data.slot][k]).isPresent()
            {
                assert process'.rcvd_attestation_shares == process_mod.rcvd_attestation_shares;            
            }
            else
            {
                assert process'.rcvd_attestation_shares == process_mod.rcvd_attestation_shares;            
            }             
        }
        else
        {             
            assert process'.rcvd_attestation_shares == process.rcvd_attestation_shares;            
        }
    }  

    lemma lemma_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_histii_c_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat        
    )
    requires add_block_to_bn.requires(process, block)
    requires process' == add_block_to_bn(process, block)    
    requires inv_g_iii_c_new_body(
                    hn, 
                    process, 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    ensures inv_g_iii_c_new_body(
                    hn, 
                    process', 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    {
        
    }
    
    lemma lemma_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_histii_c_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_g_iii_c_new_body(
                    hn, 
                    process, 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    ensures inv_g_iii_c_new_body(
                    hn, 
                    process', 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    {}

    lemma lemma_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_histii_c_f_resend_attestation_share(
        process: DVCState,
        process': DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat  
    )
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_g_iii_c_new_body(
                    hn, 
                    process, 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    ensures inv_g_iii_c_new_body(
                    hn, 
                    process', 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    { } 

    lemma lemma_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_histii_c_f_start_next_duty(
        process: DVCState, 
        attestation_duty: AttestationDuty, 
        process': DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat         
    )
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state       
    requires exists i: nat :: 
                && i < index_next_attestation_duty_to_be_served
                && var an := sequence_attestation_duties_to_be_served[i];
                && an.attestation_duty == attestation_duty
                && an.node == hn 
    requires inv_g_iii_c_new_body(
                    hn, 
                    process, 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    ensures inv_g_iii_c_new_body(
                    hn, 
                    process', 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    { } 


    lemma lemma_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_histii_c_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat  
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires && sequence_attestation_duties_to_be_served[index_next_attestation_duty_to_be_served].attestation_duty
                    == attestation_duty
             && sequence_attestation_duties_to_be_served[index_next_attestation_duty_to_be_served].node
                    == hn
    requires inv_g_iii_b_new_body(
                    hn, 
                    process, 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served
             )
    requires inv_g_iii_c_new_body(
                    hn, 
                    process, 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    ensures inv_g_iii_c_new_body(
                    hn, 
                    process', 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served + 1)
    {
        var process_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );   

        var new_index_next_attestation_duty_to_be_served := index_next_attestation_duty_to_be_served + 1;

        assert inv_g_iii_b_new_body(
                    hn, 
                    process_mod, 
                    sequence_attestation_duties_to_be_served, 
                    new_index_next_attestation_duty_to_be_served);
        assert inv_g_iii_c_new_body(
                    hn, 
                    process_mod, 
                    sequence_attestation_duties_to_be_served, 
                    new_index_next_attestation_duty_to_be_served);   
        
        lemma_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_histii_c_f_check_for_next_queued_duty(
            process_mod, 
            process',
            hn, 
            sequence_attestation_duties_to_be_served, 
            new_index_next_attestation_duty_to_be_served);        
    } 


    lemma lemma_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_histii_c_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state    
    requires inv_g_iii_b_new_body(
                    hn, 
                    process, 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served
             )
    requires inv_g_iii_c_new_body(
                    hn, 
                    process, 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served
             )
    ensures inv_g_iii_c_new_body(
                    hn, 
                    process', 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
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
                    assert inv_g_iii_b_new_body(
                                hn, 
                                process_mod, 
                                sequence_attestation_duties_to_be_served, 
                                index_next_attestation_duty_to_be_served
                    );
                    assert inv_g_iii_c_new_body(
                                hn, 
                                process_mod, 
                                sequence_attestation_duties_to_be_served, 
                                index_next_attestation_duty_to_be_served
                    );
                    
                    lemma_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_histii_c_f_check_for_next_queued_duty(
                        process_mod, 
                        process',
                        hn, 
                        sequence_attestation_duties_to_be_served, 
                        index_next_attestation_duty_to_be_served);
                }
                else
                { 
                    assert inv_g_iii_b_new_body(
                                hn, 
                                process, 
                                sequence_attestation_duties_to_be_served, 
                                index_next_attestation_duty_to_be_served
                    );
                    assert process.attestation_duties_queue[0] in process.attestation_duties_queue;
                    var i: nat :| && i < index_next_attestation_duty_to_be_served
                                  && var an := sequence_attestation_duties_to_be_served[i];
                                  && an.attestation_duty == process.attestation_duties_queue[0]
                                  && an.node == hn
                    ;

                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    );                       
                    assert inv_g_iii_b_new_body(
                                hn, 
                                process_mod, 
                                sequence_attestation_duties_to_be_served, 
                                index_next_attestation_duty_to_be_served
                    );
                    assert inv_g_iii_c_new_body(
                                hn, 
                                process_mod, 
                                sequence_attestation_duties_to_be_served, 
                                index_next_attestation_duty_to_be_served
                    );                                          
                    lemma_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_histii_c_f_start_next_duty(
                        process_mod, 
                        process.attestation_duties_queue[0], 
                        process',
                        hn, 
                        sequence_attestation_duties_to_be_served, 
                        index_next_attestation_duty_to_be_served
                    );
                }
        }
        else
        { 
            assert process'.latest_attestation_duty.isPresent() == process.latest_attestation_duty.isPresent();
            assert process.latest_attestation_duty.isPresent()
                        ==> (   process.latest_attestation_duty.safe_get()
                                == process'.latest_attestation_duty.safe_get() );
        }
    }

    lemma lemma_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_histii_c_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_g_iii_b_new_body(
                    hn, 
                    process, 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served
             )
    requires inv_g_iii_c_new_body(
                    hn, 
                    process, 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served
             )
    ensures inv_g_iii_c_new_body(
                    hn, 
                    process', 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    {
        if  && process.current_attestation_duty.isPresent()
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

    
            assert inv_g_iii_b_new_body(
                                hn, 
                                process_mod, 
                                sequence_attestation_duties_to_be_served, 
                                index_next_attestation_duty_to_be_served
                    );
            assert inv_g_iii_c_new_body(
                                hn, 
                                process_mod, 
                                sequence_attestation_duties_to_be_served, 
                                index_next_attestation_duty_to_be_served
                    );

            var ret_check_for_next_queued_duty := f_check_for_next_queued_duty(process_mod);
        
            lemma_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_histii_c_f_check_for_next_queued_duty(
                process_mod, 
                ret_check_for_next_queued_duty.state,
                hn, 
                sequence_attestation_duties_to_be_served, 
                index_next_attestation_duty_to_be_served
            );

            assert process' == ret_check_for_next_queued_duty.state;        
        }
        else
        {
            assert process' == process;
        }
    } 

    lemma lemma_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_histii_c_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_g_iii_b_new_body(
                    hn, 
                    process, 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served
             )
    requires inv_g_iii_c_new_body(
                    hn, 
                    process, 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served
             )
    ensures inv_g_iii_c_new_body(
                    hn, 
                    process', 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
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
        assert inv_g_iii_b_new_body(
                                hn, 
                                process, 
                                sequence_attestation_duties_to_be_served, 
                                index_next_attestation_duty_to_be_served
                    );
        assert inv_g_iii_c_new_body(
                                hn, 
                                process, 
                                sequence_attestation_duties_to_be_served, 
                                index_next_attestation_duty_to_be_served
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
            assert inv_g_iii_b_new_body(
                                hn, 
                                process, 
                                sequence_attestation_duties_to_be_served, 
                                index_next_attestation_duty_to_be_served
                    );
            assert inv_g_iii_c_new_body(
                                hn, 
                                process, 
                                sequence_attestation_duties_to_be_served, 
                                index_next_attestation_duty_to_be_served
                    );
            lemma_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_histii_c_f_check_for_next_queued_duty(
                process, 
                process',
                hn, 
                sequence_attestation_duties_to_be_served, 
                index_next_attestation_duty_to_be_served
            ); 
        }
        else
        {
            assert process' == process;
        }
    } 
}