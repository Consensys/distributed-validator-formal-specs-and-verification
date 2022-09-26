include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"
include "../att_spec_proofs/helper_sets_lemmas.dfy"
include "../att_spec_proofs/common_proofs.dfy"
include "../att_spec_proofs/fnc_invs_1_26.dfy"

module Fnc_Invs_27
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Att_Assumptions
    import opened Helper_Sets_Lemmas
    import opened Common_Proofs
    import opened Fnc_Invs_1_26
    
    
    

    lemma lemma_inv27_add_block_to_bn(
        s: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)    
    requires inv27_body(s)
    ensures inv27_body(s')
    { }

    lemma lemma_inv27_f_listen_for_attestation_shares(
        process: DVCNodeState,
        attestation_share: AttestationShare,
        process': DVCNodeState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv27_body(process)
    ensures inv27_body(process')
    { }

    lemma lemma_inv27_f_start_next_duty(process: DVCNodeState, attestation_duty: AttestationDuty, process': DVCNodeState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires attestation_duty in process.all_rcvd_duties
    requires inv27_body(process)
    ensures inv27_body(process')
    { } 

    lemma lemma_inv27_f_resend_attestation_share(
        process: DVCNodeState,
        process': DVCNodeState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv27_body(process)
    ensures inv27_body(process')
    { } 

    

    lemma lemma_inv27_f_check_for_next_queued_duty(
        process: DVCNodeState,
        process': DVCNodeState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state    
    requires inv5_body(process)
    requires inv25_body(process)
    requires inv27_body(process)
    ensures inv27_body(process')
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
                                        + process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys;

                    assert inv25_body(process_mod);

                    assert inv5_body(process_mod);
                    assert inv27_body(process_mod);
                    lemma_inv27_f_check_for_next_queued_duty(process_mod, process');
                }
                else
                { 
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    );     
                    assert inv5_body(process_mod);
                    assert inv27_body(process_mod);
                    lemma_inv27_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
                }
        }
        else
        { 
            assert process'.all_rcvd_duties == process.all_rcvd_duties;
        }
    }

    

    lemma lemma_inv27_f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCNodeState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv5_body(process)
    requires inv25_body(process)
    requires inv27_body(process)
    ensures inv27_body(process')
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
                            + process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys;


        assert inv5_body(process_mod);
        assert inv25_body(process_mod);

        assert inv27_body(process_mod);

        var ret_dvc := f_check_for_next_queued_duty(process_mod).state;
        lemma_inv5_f_check_for_next_queued_duty(process_mod, ret_dvc);
        assert inv5_body(ret_dvc);
        
        lemma_inv27_f_check_for_next_queued_duty(process_mod, ret_dvc);
        assert inv27_body(ret_dvc);

        assert process' == ret_dvc;        
    }

    lemma lemma_inv27_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        process': DVCNodeState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv5_body(process)
    requires inv25_body(process)
    requires inv27_body(process)
    ensures inv27_body(process')
    {
        var process_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );        

        assert inv5_body(process_mod);
        assert inv25_body(process_mod);
        assert inv27_body(process_mod);
        
        lemma_inv27_f_check_for_next_queued_duty(process_mod, process');        
    }

    lemma lemma_inv27_f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock,
        process': DVCNodeState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv5_body(process)
    requires inv25_body(process)
    requires inv27_body(process)
    ensures inv27_body(process')
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
        
        assert inv5_body(process);
        assert inv25_body(process);
        assert inv27_body(process);

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
                            + process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys;

            
            assert inv5_body(process_mod);
            assert inv25_body(process_mod);
            assert inv27_body(process_mod);

            lemma_inv27_f_check_for_next_queued_duty(process_mod, process');
        }
        else
        {               
            assert inv27_body(process);
        }
    }  

    
    lemma lemma_inv28_add_block_to_bn(
        s: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)    
    requires inv28_body(s)
    ensures inv28_body(s')
    { }

    lemma lemma_inv28_f_listen_for_attestation_shares(
        process: DVCNodeState,
        attestation_share: AttestationShare,
        process': DVCNodeState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv28_body(process)
    ensures inv28_body(process')
    { }

    lemma lemma_inv28_f_start_next_duty(process: DVCNodeState, attestation_duty: AttestationDuty, process': DVCNodeState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires attestation_duty in process.all_rcvd_duties
    requires inv28_body(process)
    ensures inv28_body(process')
    { } 

    lemma lemma_inv28_f_resend_attestation_share(
        process: DVCNodeState,
        process': DVCNodeState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv28_body(process)
    ensures inv28_body(process')
    { } 

    lemma lemma_inv28_f_check_for_next_queued_duty(
        process: DVCNodeState,
        process': DVCNodeState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state    
    requires inv5_body(process)
    requires inv26_body(process)
    requires inv28_body(process)
    ensures inv28_body(process')
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

                    assert inv28_body_ces(process.attestation_consensus_engine_state);
                    assert new_attestation_consensus_engine_state 
                                == updateConsensusInstanceValidityCheck(
                                        process.attestation_consensus_engine_state, 
                                        new_attestation_slashing_db);
                    
                    lemma_inv28_updateConsensusInstanceValidityCheck(
                        process.attestation_consensus_engine_state,
                        new_attestation_slashing_db,
                        new_attestation_consensus_engine_state);
                    assert inv28_body_ces(new_attestation_consensus_engine_state);

                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..],
                        future_att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided - {queue_head.slot},
                        attestation_slashing_db := new_attestation_slashing_db,
                        attestation_consensus_engine_state := new_attestation_consensus_engine_state                                              
                    );
                    assert inv28_body(process_mod);

                    lemma_updateConsensusInstanceValidityCheck(
                                process.attestation_consensus_engine_state,
                                new_attestation_slashing_db,
                                process_mod.attestation_consensus_engine_state 
                                );

                    assert process_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                                == process.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
                                        + process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys;
                    assert inv26_body(process_mod);
                    assert inv5_body(process_mod);

                    lemma_inv28_f_check_for_next_queued_duty(process_mod, process');
                    assert inv28_body(process');
                }
                else
                { 
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    );     
                    assert inv5_body(process_mod);
                    assert inv28_body(process_mod);
                    lemma_inv28_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
                    assert inv28_body(process');
                }
        }
        else
        { 
            assert process'.all_rcvd_duties == process.all_rcvd_duties;
            assert inv28_body(process');
        }
    }

    lemma lemma_inv28_f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCNodeState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv5_body(process)
    requires inv26_body(process)
    requires inv28_body(process)
    ensures inv28_body(process')
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
                            + process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys;


        assert inv5_body(process_mod);
        assert inv26_body(process_mod);

        assert inv28_body(process_mod);

        var ret_dvc := f_check_for_next_queued_duty(process_mod).state;
        lemma_inv5_f_check_for_next_queued_duty(process_mod, ret_dvc);
        assert inv5_body(ret_dvc);
        
        lemma_inv28_f_check_for_next_queued_duty(process_mod, ret_dvc);
        assert inv28_body(ret_dvc);

        assert process' == ret_dvc;        
    }

    lemma lemma_inv28_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        process': DVCNodeState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv5_body(process)
    requires inv26_body(process)
    requires inv28_body(process)
    ensures inv28_body(process')
    {
        var process_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );        

        assert inv5_body(process_mod);
        assert inv26_body(process_mod);
        assert inv28_body(process_mod);
        
        lemma_inv28_f_check_for_next_queued_duty(process_mod, process');        
    }

    lemma lemma_inv28_f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock,
        process': DVCNodeState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv5_body(process)
    requires inv26_body(process)
    requires inv28_body(process)
    ensures inv28_body(process')
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
        
        assert inv5_body(process);
        assert inv26_body(process);
        assert inv28_body(process);

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
                            + process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys;

            
            assert inv5_body(process_mod);
            assert inv26_body(process_mod);
            assert inv28_body(process_mod);

            lemma_inv28_f_check_for_next_queued_duty(process_mod, process');
        }
        else
        {               
            assert inv28_body(process);
        }
    } 

    lemma lemma_inv29_add_block_to_bn(
        s: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)    
    requires inv29_body(s)
    ensures inv29_body(s')
    { }

    lemma lemma_inv29_f_listen_for_attestation_shares(
        process: DVCNodeState,
        attestation_share: AttestationShare,
        process': DVCNodeState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv29_body(process)
    ensures inv29_body(process')
    { }

    lemma lemma_inv29_f_start_next_duty(process: DVCNodeState, attestation_duty: AttestationDuty, process': DVCNodeState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires attestation_duty in process.all_rcvd_duties
    requires inv29_body(process)
    ensures inv29_body(process')
    { } 

    lemma lemma_inv29_f_resend_attestation_share(
        process: DVCNodeState,
        process': DVCNodeState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv29_body(process)
    ensures inv29_body(process')
    { } 

    lemma lemma_inv29_f_check_for_next_queued_duty(
        process: DVCNodeState,
        process': DVCNodeState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state    
    requires inv5_body(process)
    requires inv25_body(process)
    requires inv29_body(process)
    ensures inv29_body(process')
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
                                        + process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys;

                    assert inv25_body(process_mod);

                    assert inv5_body(process_mod);
                    assert inv29_body(process_mod);
                    lemma_inv29_f_check_for_next_queued_duty(process_mod, process');
                }
                else
                { 
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    );     
                    assert inv5_body(process_mod);
                    assert inv29_body(process_mod);
                    lemma_inv29_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
                }
        }
        else
        { 
            assert process'.all_rcvd_duties == process.all_rcvd_duties;
        }
    }

    lemma lemma_inv29_f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCNodeState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv5_body(process)
    requires inv25_body(process)
    requires inv29_body(process)
    ensures inv29_body(process')
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
                            + process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys;


        assert inv5_body(process_mod);
        assert inv25_body(process_mod);

        assert inv29_body(process_mod);

        var ret_dvc := f_check_for_next_queued_duty(process_mod).state;
        lemma_inv5_f_check_for_next_queued_duty(process_mod, ret_dvc);
        assert inv5_body(ret_dvc);
        
        lemma_inv29_f_check_for_next_queued_duty(process_mod, ret_dvc);
        assert inv29_body(ret_dvc);

        assert process' == ret_dvc;        
    }

    lemma lemma_inv29_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        process': DVCNodeState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv5_body(process)
    requires inv25_body(process)
    requires inv29_body(process)
    ensures inv29_body(process')
    {
        var process_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );        

        assert inv5_body(process_mod);
        assert inv25_body(process_mod);
        assert inv29_body(process_mod);
        
        lemma_inv29_f_check_for_next_queued_duty(process_mod, process');        
    }

    lemma lemma_inv29_f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock,
        process': DVCNodeState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv5_body(process)
    requires inv25_body(process)
    requires inv29_body(process)
    ensures inv29_body(process')
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
        
        assert inv5_body(process);
        assert inv25_body(process);
        assert inv29_body(process);

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
                            + process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys;

            
            assert inv5_body(process_mod);
            assert inv25_body(process_mod);
            assert inv29_body(process_mod);

            lemma_inv29_f_check_for_next_queued_duty(process_mod, process');
        }
        else
        {               
            assert inv29_body(process);
        }
    }   

    lemma lemma_inv30_add_block_to_bn(
        s: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)    
    ensures s.attestation_slashing_db <= s'.attestation_slashing_db
    { }

    lemma lemma_inv30_f_listen_for_attestation_shares(
        process: DVCNodeState,
        attestation_share: AttestationShare,
        process': DVCNodeState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    ensures process.attestation_slashing_db <= process'.attestation_slashing_db    
    { }

    lemma lemma_inv30_f_start_next_duty(process: DVCNodeState, attestation_duty: AttestationDuty, process': DVCNodeState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state       
    ensures process.attestation_slashing_db <= process'.attestation_slashing_db 
    { } 

    lemma lemma_inv30_f_resend_attestation_share(
        process: DVCNodeState,
        process': DVCNodeState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    ensures process.attestation_slashing_db <= process'.attestation_slashing_db     
    { } 


    lemma lemma_inv30_f_check_for_next_queued_duty(
        process: DVCNodeState,
        process': DVCNodeState
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
                    
                    lemma_inv30_f_check_for_next_queued_duty(process_mod, process');
                }
                else
                { 
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    );     
                    assert process.attestation_slashing_db <= process_mod.attestation_slashing_db;
                    lemma_inv30_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
                }
        }
        else
        { 
            assert process.attestation_slashing_db == process'.attestation_slashing_db;
        }
    }

    lemma lemma_inv30_f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCNodeState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    ensures process.attestation_slashing_db <= process'.attestation_slashing_db
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
        
        lemma_inv30_f_check_for_next_queued_duty(process_mod, ret_dvc);
        
        assert process' == ret_dvc;        
    }

    lemma lemma_inv30_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        process': DVCNodeState
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

        lemma_inv30_f_check_for_next_queued_duty(process_mod, process');        
    }

    lemma lemma_inv30_f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock,
        process': DVCNodeState
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

            

            lemma_inv30_f_check_for_next_queued_duty(process_mod, process');
        }
        else
        { }
    } 

    lemma lemma_inv30_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')  
    ensures inv30(dvn, event, dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        lemma_inv30_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv30_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
                        lemma_inv30_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lemma_inv30_add_block_to_bn(dvc, block, dvc_mod);
                        lemma_inv30_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }

    lemma lemma_inv31_add_block_to_bn(
        s: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)    
    requires inv31_body(s)
    ensures inv31_body(s')
    { }

    lemma lemma_inv31_f_listen_for_attestation_shares(
        process: DVCNodeState,
        attestation_share: AttestationShare,
        process': DVCNodeState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv31_body(process)
    ensures inv31_body(process')
    { }

    lemma lemma_inv31_f_start_next_duty(process: DVCNodeState, attestation_duty: AttestationDuty, process': DVCNodeState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires attestation_duty in process.all_rcvd_duties
    requires inv31_body(process)
    ensures inv31_body(process')
    { } 

    lemma lemma_inv31_f_resend_attestation_share(
        process: DVCNodeState,
        process': DVCNodeState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv31_body(process)
    ensures inv31_body(process')
    { } 

    

    lemma lemma_inv31_f_check_for_next_queued_duty(
        process: DVCNodeState,
        process': DVCNodeState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state    
    requires inv5_body(process)
    requires inv26_body(process)    
    requires inv31_body(process)
    ensures inv31_body(process')
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
                    assert inv31_body_ces(process.attestation_consensus_engine_state, 
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

                    assert inv31_body_ces(process.attestation_consensus_engine_state, 
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
                    assert inv26_body(process_mod);
                    assert inv31_body_ces(process_mod.attestation_consensus_engine_state, 
                                          new_attestation_slashing_db);

                    assert inv5_body(process_mod);                    
                    assert inv31_body(process_mod);
                    lemma_inv31_f_check_for_next_queued_duty(process_mod, process');
                }
                else
                { 
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    );     
                    assert inv5_body(process_mod);
                    assert inv31_body(process_mod);
                    lemma_inv31_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
                }
        }
        else
        { 
            assert inv31_body(process');
        }
    }

    lemma lemma_inv31_f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCNodeState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv5_body(process)
    requires inv26_body(process)
    requires inv31_body(process)
    ensures inv31_body(process')
    {
        
        var local_current_attestation_duty := process.current_attestation_duty.safe_get();
        var attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);
        assert process.attestation_slashing_db <= attestation_slashing_db;
        assert inv31_body_ces(process.attestation_consensus_engine_state, 
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

        assert inv31_body_ces(process.attestation_consensus_engine_state, 
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

        assert inv26_body(process);


        lemma_inv31_updateConsensusInstanceValidityCheck(
                                process.attestation_consensus_engine_state,
                                attestation_slashing_db,
                                new_attestation_consensus_engine_state
                                );


        assert inv31_body_ces(new_attestation_consensus_engine_state, attestation_slashing_db);

        var process_mod := 
            process.(
                current_attestation_duty := None,
                attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                attestation_slashing_db := attestation_slashing_db,
                attestation_consensus_engine_state := new_attestation_consensus_engine_state
            );

        assert inv31_body(process_mod);
    
        var ret_dvc := f_check_for_next_queued_duty(process_mod).state;
        lemma_inv5_f_check_for_next_queued_duty(process_mod, ret_dvc);
        assert inv5_body(ret_dvc);
        
        
        lemma_inv31_f_check_for_next_queued_duty(process_mod, ret_dvc);
        assert inv31_body(ret_dvc);

        assert process' == ret_dvc;        
    }

    lemma lemma_inv31_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        process': DVCNodeState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv5_body(process)
    requires inv26_body(process)
    requires inv31_body(process)
    ensures inv31_body(process')
    {
        var process_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );        

        assert inv5_body(process_mod);
        assert inv26_body(process_mod);
        assert inv31_body(process_mod);
        
        lemma_inv31_f_check_for_next_queued_duty(process_mod, process');        
    }

    lemma lemma_inv31_f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock,
        process': DVCNodeState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv5_body(process)
    requires inv26_body(process)
    requires inv31_body(process)
    ensures inv31_body(process')
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
        
        assert inv5_body(process);
        assert inv26_body(process);
        assert inv31_body(process);

        if process.current_attestation_duty.isPresent() && process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            var decided_attestation_data := att_consensus_instances_already_decided[process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);

            assert process.attestation_slashing_db <= new_attestation_slashing_db;
            assert inv31_body_ces(process.attestation_consensus_engine_state, 
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

            assert inv31_body_ces(process.attestation_consensus_engine_state, 
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
                            + process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys;

            
            assert inv5_body(process_mod);
            assert inv26_body(process_mod);
            assert inv31_body(process_mod);

            lemma_inv31_f_check_for_next_queued_duty(process_mod, process');
        }
        else
        {               
            assert inv31_body(process);
        }
    }   
    
    lemma lemma_inv32_add_block_to_bn(
        s: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)    
    ensures inv32_body(s, s')
    { }

    lemma lemma_inv32_f_listen_for_attestation_shares(
        process: DVCNodeState,
        attestation_share: AttestationShare,
        process': DVCNodeState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    ensures inv32_body(process, process')
    { }

    lemma lemma_inv32_f_start_next_duty(process: DVCNodeState, attestation_duty: AttestationDuty, process': DVCNodeState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state       
    ensures inv32_body(process, process')
    { } 

    lemma lemma_inv32_f_resend_attestation_share(
        process: DVCNodeState,
        process': DVCNodeState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    ensures inv32_body(process, process')     
    { } 


    lemma lemma_inv32_f_check_for_next_queued_duty(
        process: DVCNodeState,
        process': DVCNodeState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state        
    ensures inv32_body(process, process')
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
                    
                    lemma_inv32_f_check_for_next_queued_duty(process_mod, process');
                }
                else
                { 
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    );     
                    assert process.attestation_slashing_db <= process_mod.attestation_slashing_db;
                    lemma_inv32_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
                }
        }
        else
        { 
            assert process.attestation_slashing_db == process'.attestation_slashing_db;
        }
    }

    lemma lemma_inv32_f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCNodeState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    ensures inv32_body(process, process')
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
        
        lemma_inv32_f_check_for_next_queued_duty(process_mod, ret_dvc);
        
        assert process' == ret_dvc;        
    }

    lemma lemma_inv32_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        process': DVCNodeState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    ensures inv32_body(process, process')
    {
        var process_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );        

        assert process.attestation_slashing_db <= process_mod.attestation_slashing_db;

        lemma_inv32_f_check_for_next_queued_duty(process_mod, process');        
    }

    lemma lemma_inv32_f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock,
        process': DVCNodeState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state   
    ensures inv32_body(process, process')    
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

            

            lemma_inv32_f_check_for_next_queued_duty(process_mod, process');
        }
        else
        { }
    } 


    /*
    lemma lemma_inv33_add_block_to_bn(
        s: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState,
        k: Slot
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)    
    requires inv33_body(s, k)
    ensures inv33_body(s', k)
    { }

    lemma lemma_inv33_f_listen_for_attestation_shares(
        process: DVCNodeState,
        attestation_share: AttestationShare,
        process': DVCNodeState,
        k: Slot
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv33_body(process, k)
    ensures inv33_body(process', k)
    { }

    lemma lemma_inv33_f_start_next_duty(
                process: DVCNodeState, 
                attestation_duty: AttestationDuty, 
                process': DVCNodeState,
                k: Slot)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires attestation_duty in process.all_rcvd_duties
    requires inv33_body(process, k)
    ensures inv33_body(process', k)
    { } 

    lemma lemma_inv33_f_resend_attestation_share(
        process: DVCNodeState,
        process': DVCNodeState,
        k: Slot)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv33_body(process, k)
    ensures inv33_body(process', k)
    { } 

    lemma lemma_inv33_f_check_for_next_queued_duty(
        process: DVCNodeState,
        process': DVCNodeState,
        k: Slot
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state    
    requires inv5_body(process)
    requires inv25_body(process)
    requires inv33_body(process, k)
    ensures inv33_body(process', k)
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
                                        + process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys;

                    assert inv25_body(process_mod);

                    assert inv5_body(process_mod);
                    assert inv33_body(process_mod, k);
                    lemma_inv33_f_check_for_next_queued_duty(process_mod, process', k);
                }
                else
                { 
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    );     
                    assert inv5_body(process_mod);
                    assert inv33_body(process_mod, k);
                    lemma_inv33_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process', k);
                }
        }
        else
        { 
            assert process'.all_rcvd_duties == process.all_rcvd_duties;
        }
    }

    lemma lemma_inv33_f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCNodeState,
        k: Slot
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv5_body(process)
    requires inv25_body(process)
    requires inv33_body(process, k)
    ensures inv33_body(process', k)
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
                            + process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys;


        assert inv5_body(process_mod);
        assert inv25_body(process_mod);

        assert inv33_body(process_mod, k);

        var ret_dvc := f_check_for_next_queued_duty(process_mod).state;
        lemma_inv5_f_check_for_next_queued_duty(process_mod, ret_dvc);
        assert inv5_body(ret_dvc);
        
        lemma_inv33_f_check_for_next_queued_duty(process_mod, ret_dvc, k);
        assert inv33_body(ret_dvc, k);

        assert process' == ret_dvc;        
    }

    lemma lemma_inv33_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        process': DVCNodeState,
        k: Slot
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv5_body(process)
    requires inv25_body(process)
    requires inv33_body(process, k)
    ensures inv33_body(process', k)
    {
        var process_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );        

        assert inv5_body(process_mod);
        assert inv25_body(process_mod);
        assert inv33_body(process_mod, k);
        
        lemma_inv33_f_check_for_next_queued_duty(process_mod, process', k);        
    }

    lemma lemma_inv33_f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock,
        process': DVCNodeState,
        k: Slot
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv5_body(process)
    requires inv25_body(process)
    requires inv33_body(process, k)
    ensures inv33_body(process', k)
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
        
        assert inv5_body(process);
        assert inv25_body(process);
        assert inv33_body(process, k);

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
                            + process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys;

            
            assert inv5_body(process_mod);
            assert inv25_body(process_mod);
            assert inv33_body(process_mod, k);

            lemma_inv33_f_check_for_next_queued_duty(process_mod, process', k);
        }
        else
        {               
            assert inv33_body(process, k);
        }
    }
    */
}