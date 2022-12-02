include "../../../../common/commons.dfy"
include "../../common/attestation_creation_instrumented.dfy"
include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_attestation_creation.dfy"
include "../inv.dfy"
include "../../../common/helper_sets_lemmas.dfy"
include "../../common/common_proofs.dfy"
include "../../common/dvc_spec_axioms.dfy"

include "../../../common/helper_pred_fcn.dfy"


module Fnc_Invs_1
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
    import opened DVC_Spec_Axioms
    import opened Helper_Pred_Fcn

    
    lemma lem_inv_queued_att_duty_is_dvn_seq_of_att_duty_f_serve_attestation_duty(
        dvc: DVCState,
        attestation_duty: AttestationDuty,
        dvc': DVCState
    )  
    requires f_serve_attestation_duty.requires(dvc, attestation_duty)
    requires dvc' == f_serve_attestation_duty(dvc, attestation_duty).state
    ensures dvc'.all_rcvd_duties == dvc.all_rcvd_duties + {attestation_duty}    
    {
        var dvc_mod := f_enqueue_new_att_duty(
                                dvc,
                                attestation_duty
                            );       

        lem_inv_queued_att_duty_is_dvn_seq_of_att_duty_f_check_for_next_queued_duty(dvc_mod, dvc');        
    }

    lemma lem_inv_queued_att_duty_is_dvn_seq_of_att_duty_f_check_for_next_queued_duty(
        dvc: DVCState,
        dvc': DVCState
    )
    requires f_check_for_next_queued_duty.requires(dvc)
    requires dvc' == f_check_for_next_queued_duty(dvc).state
    ensures dvc'.all_rcvd_duties == dvc.all_rcvd_duties
    decreases dvc.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(dvc)   
        {            
            if first_queued_att_duty_was_decided(dvc)
            {
                var dvc_mod := f_dequeue_attestation_duties_queue(dvc);
                lem_inv_queued_att_duty_is_dvn_seq_of_att_duty_f_check_for_next_queued_duty(dvc_mod, dvc');
            }
            else
            { 
                var dvc_mod := dvc.(
                    attestation_duties_queue := dvc.attestation_duties_queue[1..]
                );         
                lem_inv_queued_att_duty_is_dvn_seq_of_att_duty_f_start_next_duty(dvc_mod, dvc.attestation_duties_queue[0], dvc');
            }
        }
        else
        { 
            assert dvc'.all_rcvd_duties == dvc.all_rcvd_duties;
        }
    }

    lemma lem_inv_queued_att_duty_is_dvn_seq_of_att_duty_f_start_next_duty(dvc: DVCState, attestation_duty: AttestationDuty, dvc': DVCState)
    requires f_start_next_duty.requires(dvc, attestation_duty)
    requires dvc' == f_start_next_duty(dvc, attestation_duty).state
    ensures dvc'.all_rcvd_duties == dvc.all_rcvd_duties        
    {  
        assert dvc'.all_rcvd_duties == dvc.all_rcvd_duties;
    }  

    lemma lem_inv_queued_att_duty_is_dvn_seq_of_att_duty_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state 
    ensures process'.all_rcvd_duties == process.all_rcvd_duties
    {
        
        if  pred_curr_att_duty_has_been_decided(process, id)
        {
            var process_mod := f_update_process_after_att_duty_decided(
                                process,
                                id,
                                decided_attestation_data);

            var ret_check_for_next_queued_duty := f_check_for_next_queued_duty(process_mod);
            
            lem_inv_queued_att_duty_is_dvn_seq_of_att_duty_f_check_for_next_queued_duty(process_mod, ret_check_for_next_queued_duty.state);

            assert process' == ret_check_for_next_queued_duty.state;
        } 
    }  


    lemma lem_inv_queued_att_duty_is_dvn_seq_of_att_duty_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    ensures process.all_rcvd_duties == process'.all_rcvd_duties
    {}

    lemma lem_inv_queued_att_duty_is_dvn_seq_of_att_duty_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
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
                f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                process,
                                block
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
            lem_inv_queued_att_duty_is_dvn_seq_of_att_duty_f_check_for_next_queued_duty(process, process');
        }
        else
        {}
    }   

    lemma lem_inv_queued_att_duty_is_dvn_seq_of_att_duty_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)
    requires s.all_rcvd_duties == s'.all_rcvd_duties
    { } 

    lemma lem_inv_queued_att_duty_is_rcvd_duty_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)
    requires inv_queued_att_duty_is_rcvd_duty_body(s)
    ensures inv_queued_att_duty_is_rcvd_duty_body(s')
    { } 
    
    lemma lem_inv_queued_att_duty_is_rcvd_duty_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    ensures inv_queued_att_duty_is_rcvd_duty_body(process')
    { }  

    lemma lem_inv_queued_att_duty_is_rcvd_duty_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    ensures inv_queued_att_duty_is_rcvd_duty_body(process')
    decreases process.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(process)
        {            
            if first_queued_att_duty_was_decided(process)
            {
                var process_mod := f_dequeue_attestation_duties_queue(process);
                lem_inv_queued_att_duty_is_rcvd_duty_f_check_for_next_queued_duty(process_mod, process');
            }
            else
            { 
                var process_mod := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..]
                );         
                lem_inv_queued_att_duty_is_rcvd_duty_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
            }
        }
        else
        { 
            assert process'.all_rcvd_duties == process.all_rcvd_duties;
        }
    }

    lemma lem_inv_queued_att_duty_is_rcvd_duty_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    ensures inv_queued_att_duty_is_rcvd_duty_body(process')
    {
        var process_mod := f_enqueue_new_att_duty(
                                    process,
                                    attestation_duty
                                );

        assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);

        lem_inv_queued_att_duty_is_rcvd_duty_f_check_for_next_queued_duty(process_mod, process');        
    }    

    lemma lem_inv_queued_att_duty_is_rcvd_duty_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state 
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    ensures inv_queued_att_duty_is_rcvd_duty_body(process')
    {
        
        if  pred_curr_att_duty_has_been_decided(process, id)
        {
            var process_mod := f_update_process_after_att_duty_decided(
                                process,
                                id,
                                decided_attestation_data);

            assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);

            var ret_check_for_next_queued_duty := f_check_for_next_queued_duty(process_mod);
            
            lem_inv_queued_att_duty_is_rcvd_duty_f_check_for_next_queued_duty(process_mod, ret_check_for_next_queued_duty.state);

            assert process' == ret_check_for_next_queued_duty.state;
        }
    }  

    lemma lem_inv_queued_att_duty_is_rcvd_duty_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    ensures inv_queued_att_duty_is_rcvd_duty_body(process')
    {}

    lemma lem_inv_queued_att_duty_is_rcvd_duty_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    ensures inv_queued_att_duty_is_rcvd_duty_body(process')
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var process :=
                f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                process,
                                block
                            );      

        assert inv_queued_att_duty_is_rcvd_duty_body(process);
                    

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

            assert inv_queued_att_duty_is_rcvd_duty_body(process);

            lem_inv_queued_att_duty_is_rcvd_duty_f_check_for_next_queued_duty(process, process');
        }
        else
        {
            assert inv_queued_att_duty_is_rcvd_duty_body(process);
        }
    }  

    lemma lem_inv_current_att_duty_is_rcvd_duty_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state    
    requires attestation_duty in process.all_rcvd_duties
    requires inv_current_att_duty_is_rcvd_duty_body(process)
    ensures inv_current_att_duty_is_rcvd_duty_body(process')
    { }  

    lemma lem_inv_current_att_duty_is_rcvd_duty_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_current_att_duty_is_rcvd_duty_body(process)
    ensures inv_current_att_duty_is_rcvd_duty_body(process')
    decreases process.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(process)    
        {            
            if first_queued_att_duty_was_decided(process)
            {
                var process_mod := f_dequeue_attestation_duties_queue(process);
                lem_inv_current_att_duty_is_rcvd_duty_f_check_for_next_queued_duty(process_mod, process');
            }
            else
            { 
                var process_mod := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..]
                );     
                assert process.attestation_duties_queue[0] in process.all_rcvd_duties;
                lem_inv_current_att_duty_is_rcvd_duty_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
            }
        }
        else
        { 
            assert process'.all_rcvd_duties == process.all_rcvd_duties;
        }
    }

    lemma lem_inv_current_att_duty_is_rcvd_duty_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_current_att_duty_is_rcvd_duty_body(process)
    ensures inv_current_att_duty_is_rcvd_duty_body(process')
    {
        var process_mod := f_enqueue_new_att_duty(
                                    process,
                                    attestation_duty
                                );

        assert inv_current_att_duty_is_rcvd_duty_body(process_mod);

        lem_inv_current_att_duty_is_rcvd_duty_f_check_for_next_queued_duty(process_mod, process');        
    } 

    lemma lem_inv_current_att_duty_is_rcvd_duty_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state 
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_current_att_duty_is_rcvd_duty_body(process)
    ensures inv_current_att_duty_is_rcvd_duty_body(process')
    {
        
        if  pred_curr_att_duty_has_been_decided(process, id)
        {
            var process_mod := f_update_process_after_att_duty_decided(
                                process,
                                id,
                                decided_attestation_data);

            assert inv_current_att_duty_is_rcvd_duty_body(process_mod);

            var ret_check_for_next_queued_duty := f_check_for_next_queued_duty(process_mod);
            
            lem_inv_current_att_duty_is_rcvd_duty_f_check_for_next_queued_duty(process_mod, ret_check_for_next_queued_duty.state);

            assert process' == ret_check_for_next_queued_duty.state;
        }        
    }  

    lemma lem_inv_current_att_duty_is_rcvd_duty_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_current_att_duty_is_rcvd_duty_body(process)
    ensures inv_current_att_duty_is_rcvd_duty_body(process')
    {}

    lemma lem_inv_current_att_duty_is_rcvd_duty_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_current_att_duty_is_rcvd_duty_body(process)
    ensures inv_current_att_duty_is_rcvd_duty_body(process')
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var process :=
                f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                process,
                                block
                            );      

        assert inv_current_att_duty_is_rcvd_duty_body(process);
                    

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

            assert inv_queued_att_duty_is_rcvd_duty_body(process);
            assert inv_current_att_duty_is_rcvd_duty_body(process);

            lem_inv_current_att_duty_is_rcvd_duty_f_check_for_next_queued_duty(process, process');
        }
        else
        {   
            assert inv_current_att_duty_is_rcvd_duty_body(process);
        }
    }  

    lemma lem_inv_latest_served_duty_is_rcvd_duty_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state    
    requires attestation_duty in process.all_rcvd_duties
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    { }  

    lemma lem_inv_latest_served_duty_is_rcvd_duty_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    decreases process.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(process)    
        {            
            if first_queued_att_duty_was_decided(process)
            {
                var process_mod := f_dequeue_attestation_duties_queue(process);
                lem_inv_latest_served_duty_is_rcvd_duty_f_check_for_next_queued_duty(process_mod, process');
            }
            else
            { 
                var process_mod := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..]
                );     
                assert process.attestation_duties_queue[0] in process.all_rcvd_duties;
                lem_inv_latest_served_duty_is_rcvd_duty_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
            }
        }
        else
        { 
            assert process'.all_rcvd_duties == process.all_rcvd_duties;
        }
    }

    lemma lem_inv_latest_served_duty_is_rcvd_duty_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    {
        var process_mod := f_enqueue_new_att_duty(
                                    process,
                                    attestation_duty
                                );

        assert inv_latest_served_duty_is_rcvd_duty_body(process_mod);

        lem_inv_latest_served_duty_is_rcvd_duty_f_check_for_next_queued_duty(process_mod, process');        
    } 

    lemma lem_inv_latest_served_duty_is_rcvd_duty_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state 
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    {
        
        if  pred_curr_att_duty_has_been_decided(process, id)
        {
            var process_mod := f_update_process_after_att_duty_decided(
                                process,
                                id,
                                decided_attestation_data);

            assert inv_latest_served_duty_is_rcvd_duty_body(process_mod);

            var ret_check_for_next_queued_duty := f_check_for_next_queued_duty(process_mod);
            
            lem_inv_latest_served_duty_is_rcvd_duty_f_check_for_next_queued_duty(process_mod, ret_check_for_next_queued_duty.state);

            assert process' == ret_check_for_next_queued_duty.state;
        }
        
    }  

    lemma lem_inv_latest_served_duty_is_rcvd_duty_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    {}

    lemma lem_inv_latest_served_duty_is_rcvd_duty_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var process :=
                f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                process,
                                block
                            );      

        assert inv_latest_served_duty_is_rcvd_duty_body(process);
                    

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

            assert inv_queued_att_duty_is_rcvd_duty_body(process);
            assert inv_latest_served_duty_is_rcvd_duty_body(process);

            lem_inv_latest_served_duty_is_rcvd_duty_f_check_for_next_queued_duty(process, process');
        }
        else
        {   
            assert inv_latest_served_duty_is_rcvd_duty_body(process);
        }
    }

    lemma lem_inv_none_latest_served_duty_implies_none_current_att_duty_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state        
    requires inv_none_latest_served_duty_implies_none_current_att_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_att_duty_body(process')
    { }  

    lemma lem_inv_none_latest_served_duty_implies_none_current_att_duty_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state    
    requires inv_none_latest_served_duty_implies_none_current_att_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_att_duty_body(process')
    decreases process.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(process)    
        {            
            if first_queued_att_duty_was_decided(process)
            {
                var process_mod := f_dequeue_attestation_duties_queue(process); 
                lem_inv_none_latest_served_duty_implies_none_current_att_duty_f_check_for_next_queued_duty(process_mod, process');
            }
            else
            { 
                var process_mod := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..]
                );     
                assert inv_none_latest_served_duty_implies_none_current_att_duty_body(process_mod);
                lem_inv_none_latest_served_duty_implies_none_current_att_duty_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
            }
        }
        else
        { 
            assert process'.all_rcvd_duties == process.all_rcvd_duties;
        }
    }

    lemma lem_inv_none_latest_served_duty_implies_none_current_att_duty_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_none_latest_served_duty_implies_none_current_att_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_att_duty_body(process')
    {
        var process_mod := f_enqueue_new_att_duty(
                                    process,
                                    attestation_duty
                                );
        

        lem_inv_none_latest_served_duty_implies_none_current_att_duty_f_check_for_next_queued_duty(process_mod, process');        
    } 

    lemma lem_inv_none_latest_served_duty_implies_none_current_att_duty_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state     
    requires inv_none_latest_served_duty_implies_none_current_att_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_att_duty_body(process')
    {
        
        if  pred_curr_att_duty_has_been_decided(process, id)
        {
            var process_mod := f_update_process_after_att_duty_decided(
                                process,
                                id,
                                decided_attestation_data);

            assert inv_none_latest_served_duty_implies_none_current_att_duty_body(process_mod);

            var ret_check_for_next_queued_duty := f_check_for_next_queued_duty(process_mod);
            
            lem_inv_none_latest_served_duty_implies_none_current_att_duty_f_check_for_next_queued_duty(process_mod, ret_check_for_next_queued_duty.state);

            assert process' == ret_check_for_next_queued_duty.state;
        }
    }  

    lemma lem_inv_none_latest_served_duty_implies_none_current_att_duty_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_none_latest_served_duty_implies_none_current_att_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_att_duty_body(process')
    {}

    lemma lem_inv_none_latest_served_duty_implies_none_current_att_duty_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state    
    requires inv_none_latest_served_duty_implies_none_current_att_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_att_duty_body(process')
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var process :=
                f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                process,
                                block
                            );      

        assert inv_none_latest_served_duty_implies_none_current_att_duty_body(process);
                    

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
            
            assert inv_none_latest_served_duty_implies_none_current_att_duty_body(process);

            lem_inv_none_latest_served_duty_implies_none_current_att_duty_f_check_for_next_queued_duty(process, process');
        }
        else
        {   
            assert inv_none_latest_served_duty_implies_none_current_att_duty_body(process);
        }
    }  

    lemma lem_inv_none_latest_served_duty_implies_none_current_att_duty_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state    
    requires inv_none_latest_served_duty_implies_none_current_att_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_att_duty_body(process')
    { }       
         
    lemma lem_inv_none_latest_served_duty_implies_none_current_att_duty_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)
    requires inv_none_latest_served_duty_implies_none_current_att_duty_body(s)
    ensures inv_none_latest_served_duty_implies_none_current_att_duty_body(s')
    { }    

    lemma lem_inv_current_att_duty_is_either_none_or_latest_served_duty_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state        
    requires inv_current_att_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_att_duty_is_either_none_or_latest_served_duty_body(process')
    { }  

    lemma lem_inv_current_att_duty_is_either_none_or_latest_served_duty_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state    
    requires inv_current_att_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_att_duty_is_either_none_or_latest_served_duty_body(process')
    decreases process.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(process)    
        {            
            if first_queued_att_duty_was_decided(process)
            {
                var process_mod := f_dequeue_attestation_duties_queue(process);
                lem_inv_current_att_duty_is_either_none_or_latest_served_duty_f_check_for_next_queued_duty(process_mod, process');
            }
            else
            { 
                var process_mod := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..]
                );     
                assert inv_current_att_duty_is_either_none_or_latest_served_duty_body(process_mod);

                lem_inv_current_att_duty_is_either_none_or_latest_served_duty_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
            }
        }
        else
        { 
            assert process'.all_rcvd_duties == process.all_rcvd_duties;
        }
    }

    lemma lem_inv_current_att_duty_is_either_none_or_latest_served_duty_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_none_latest_served_duty_implies_none_current_att_duty_body(process)  
    requires inv_current_att_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_att_duty_is_either_none_or_latest_served_duty_body(process')
    {
        var process_mod := f_enqueue_new_att_duty(
                                    process,
                                    attestation_duty
                                );
        
        lem_inv_current_att_duty_is_either_none_or_latest_served_duty_f_check_for_next_queued_duty(process_mod, process');        
    } 

    lemma lem_inv_current_att_duty_is_either_none_or_latest_served_duty_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state     
    requires inv_current_att_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_att_duty_is_either_none_or_latest_served_duty_body(process')
    {
        
        if  pred_curr_att_duty_has_been_decided(process, id)
        {
            var process_mod := f_update_process_after_att_duty_decided(
                                process,
                                id,
                                decided_attestation_data);


            assert inv_current_att_duty_is_either_none_or_latest_served_duty_body(process_mod);

            var ret_check_for_next_queued_duty := f_check_for_next_queued_duty(process_mod);
            
            lem_inv_current_att_duty_is_either_none_or_latest_served_duty_f_check_for_next_queued_duty(process_mod, ret_check_for_next_queued_duty.state);

            assert process' == ret_check_for_next_queued_duty.state;
        }
    }  

    lemma lem_inv_current_att_duty_is_either_none_or_latest_served_duty_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_current_att_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_att_duty_is_either_none_or_latest_served_duty_body(process')
    {}

    lemma lem_inv_current_att_duty_is_either_none_or_latest_served_duty_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state    
    requires inv_current_att_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_att_duty_is_either_none_or_latest_served_duty_body(process')
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var process :=
                f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                process,
                                block
                            );      

        assert inv_current_att_duty_is_either_none_or_latest_served_duty_body(process);
                    

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
            
            assert inv_current_att_duty_is_either_none_or_latest_served_duty_body(process);

            lem_inv_current_att_duty_is_either_none_or_latest_served_duty_f_check_for_next_queued_duty(process, process');
        }
        else
        {   
            assert inv_current_att_duty_is_either_none_or_latest_served_duty_body(process);
        }
    }  

    lemma lem_inv_current_att_duty_is_either_none_or_latest_served_duty_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state    
    requires inv_current_att_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_att_duty_is_either_none_or_latest_served_duty_body(process')
    { }       
         
    lemma lem_inv_current_att_duty_is_either_none_or_latest_served_duty_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)
    requires inv_current_att_duty_is_either_none_or_latest_served_duty_body(s)
    ensures inv_current_att_duty_is_either_none_or_latest_served_duty_body(s')
    { }

    lemma lem_inv_not_none_current_att_duty_is_latest_served_att_duty_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state        
    requires inv_not_none_current_att_duty_is_latest_served_att_duty_body(process)
    ensures inv_not_none_current_att_duty_is_latest_served_att_duty_body(process')
    { }  

    lemma lem_inv_not_none_current_att_duty_is_latest_served_att_duty_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state    
    requires inv_not_none_current_att_duty_is_latest_served_att_duty_body(process)
    ensures inv_not_none_current_att_duty_is_latest_served_att_duty_body(process')
    decreases process.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(process)    
        {            
            if first_queued_att_duty_was_decided(process)
            {
                var process_mod := f_dequeue_attestation_duties_queue(process);
                lem_inv_not_none_current_att_duty_is_latest_served_att_duty_f_check_for_next_queued_duty(process_mod, process');
            }
            else
            { 
                var process_mod := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..]
                );     
                assert inv_not_none_current_att_duty_is_latest_served_att_duty_body(process_mod);
                lem_inv_not_none_current_att_duty_is_latest_served_att_duty_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
            }
        }
        else
        { 
            assert process'.all_rcvd_duties == process.all_rcvd_duties;
        }
    }

    lemma lem_inv_not_none_current_att_duty_is_latest_served_att_duty_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_none_latest_served_duty_implies_none_current_att_duty_body(process)  
    requires inv_not_none_current_att_duty_is_latest_served_att_duty_body(process)
    ensures inv_not_none_current_att_duty_is_latest_served_att_duty_body(process')
    {
        var process_mod := f_enqueue_new_att_duty(
                                    process,
                                    attestation_duty
                                );
        
        lem_inv_not_none_current_att_duty_is_latest_served_att_duty_f_check_for_next_queued_duty(process_mod, process');        
    } 

    lemma lem_inv_not_none_current_att_duty_is_latest_served_att_duty_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state     
    requires inv_not_none_current_att_duty_is_latest_served_att_duty_body(process)
    ensures inv_not_none_current_att_duty_is_latest_served_att_duty_body(process')
    {
        
        if pred_curr_att_duty_has_been_decided(process, id)
        {
            var process_mod := f_update_process_after_att_duty_decided(
                                    process,
                                    id,
                                    decided_attestation_data);

            assert inv_not_none_current_att_duty_is_latest_served_att_duty_body(process_mod);

            var ret_check_for_next_queued_duty := f_check_for_next_queued_duty(process_mod);
            
            lem_inv_not_none_current_att_duty_is_latest_served_att_duty_f_check_for_next_queued_duty(process_mod, ret_check_for_next_queued_duty.state);

            assert process' == ret_check_for_next_queued_duty.state;
        }
    }  

    lemma lem_inv_not_none_current_att_duty_is_latest_served_att_duty_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_not_none_current_att_duty_is_latest_served_att_duty_body(process)
    ensures inv_not_none_current_att_duty_is_latest_served_att_duty_body(process')
    {}

    lemma lem_inv_not_none_current_att_duty_is_latest_served_att_duty_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state    
    requires inv_not_none_current_att_duty_is_latest_served_att_duty_body(process)
    ensures inv_not_none_current_att_duty_is_latest_served_att_duty_body(process')
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var process :=
                f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                process,
                                block
                            );      

        assert inv_not_none_current_att_duty_is_latest_served_att_duty_body(process);
                    

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
            
            assert inv_not_none_current_att_duty_is_latest_served_att_duty_body(process);

            lem_inv_not_none_current_att_duty_is_latest_served_att_duty_f_check_for_next_queued_duty(process, process');
        }
        else
        {   
            assert inv_not_none_current_att_duty_is_latest_served_att_duty_body(process);
        }
    }  

    lemma lem_inv_not_none_current_att_duty_is_latest_served_att_duty_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state    
    requires inv_not_none_current_att_duty_is_latest_served_att_duty_body(process)
    ensures inv_not_none_current_att_duty_is_latest_served_att_duty_body(process')
    { }       
         
    lemma lem_inv_not_none_current_att_duty_is_latest_served_att_duty_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)
    requires inv_not_none_current_att_duty_is_latest_served_att_duty_body(s)
    ensures inv_not_none_current_att_duty_is_latest_served_att_duty_body(s')
    { }

    lemma lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state        
    requires inv_none_latest_served_duty_implies_none_current_att_duty_body(process) || inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process)
    ensures inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process')
    { }  

    lemma lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state    
    requires inv_none_latest_served_duty_implies_none_current_att_duty_body(process) || inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process)
    ensures inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process')
    decreases process.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(process)    
        {            
            if first_queued_att_duty_was_decided(process)
            {
                var process_mod := f_dequeue_attestation_duties_queue(process);
                lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_check_for_next_queued_duty(process_mod, process');
            }
            else
            { 
                var process_mod := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..]
                );     
                assert inv_none_latest_served_duty_implies_none_current_att_duty_body(process_mod) || inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process_mod);

                lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
            }
        }
        else
        { 
            assert process'.all_rcvd_duties == process.all_rcvd_duties;
        }
    }

    lemma lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_none_latest_served_duty_implies_none_current_att_duty_body(process)  
    requires inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process)
    ensures inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process')
    {
        var process_mod := f_enqueue_new_att_duty(
                                    process,
                                    attestation_duty
                                );
        
        lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_check_for_next_queued_duty(process_mod, process');        
    } 

    lemma lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state     
    requires inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process)
    ensures inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process')
    {
        
        if pred_curr_att_duty_has_been_decided(process, id)
        {
            var process_mod := f_update_process_after_att_duty_decided(
                                    process,
                                    id,
                                    decided_attestation_data);

            assert inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process_mod);

            var ret_check_for_next_queued_duty := f_check_for_next_queued_duty(process_mod);
            
            lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_check_for_next_queued_duty(process_mod, ret_check_for_next_queued_duty.state);

            assert process' == ret_check_for_next_queued_duty.state;
        }
        
    }  

    lemma lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process)
    ensures inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process')
    {}

    lemma lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state    
    requires inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process)
    ensures inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process')
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var process :=
                f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                process,
                                block
                            );      

        assert inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process);
                    

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
            
            assert inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process);

            lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_check_for_next_queued_duty(process, process');
        }
        else
        {   
            assert inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process);
        }
    }  

    lemma lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state    
    requires inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process)
    ensures inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process')
    { }       
         
    lemma lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)
    requires inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(s)
    ensures inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(s')
    { }

    lemma lem_inv_strictly_increasing_queue_of_att_duties_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state        
    requires inv_strictly_increasing_queue_of_att_duties_body(process)
    ensures inv_strictly_increasing_queue_of_att_duties_body(process')
    { }  

    lemma lem_inv_strictly_increasing_queue_of_att_duties_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state    
    requires inv_strictly_increasing_queue_of_att_duties_body(process)
    ensures inv_strictly_increasing_queue_of_att_duties_body(process')
    decreases process.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(process)    
        {            
            if first_queued_att_duty_was_decided(process)
            {
                var process_mod := f_dequeue_attestation_duties_queue(process);
                lem_inv_strictly_increasing_queue_of_att_duties_f_check_for_next_queued_duty(process_mod, process');
            }
            else
            { 
                var process_mod := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..]
                );     
                assert inv_none_latest_served_duty_implies_none_current_att_duty_body(process_mod) || inv_strictly_increasing_queue_of_att_duties_body(process_mod);

                lem_inv_strictly_increasing_queue_of_att_duties_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
            }
        }
        else
        { 
            assert process'.all_rcvd_duties == process.all_rcvd_duties;
        }
    }

    lemma lem_inv_strictly_increasing_queue_of_att_duties_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_strictly_increasing_queue_of_att_duties_body(process)
    ensures inv_strictly_increasing_queue_of_att_duties_body(process')
    {}

    lemma lem_inv_strictly_increasing_queue_of_att_duties_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state    
    requires inv_strictly_increasing_queue_of_att_duties_body(process)
    ensures inv_strictly_increasing_queue_of_att_duties_body(process')
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var process :=
                f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                process,
                                block
                            );      

        assert inv_strictly_increasing_queue_of_att_duties_body(process);
                    

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
            
            assert inv_strictly_increasing_queue_of_att_duties_body(process);

            lem_inv_strictly_increasing_queue_of_att_duties_f_check_for_next_queued_duty(process, process');
        }
        else
        {   
            assert inv_strictly_increasing_queue_of_att_duties_body(process);
        }
    }  

    lemma lem_inv_strictly_increasing_queue_of_att_duties_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state    
    requires inv_strictly_increasing_queue_of_att_duties_body(process)
    ensures inv_strictly_increasing_queue_of_att_duties_body(process')
    { }       
         
    lemma lem_inv_strictly_increasing_queue_of_att_duties_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)
    requires inv_strictly_increasing_queue_of_att_duties_body(s)
    ensures inv_strictly_increasing_queue_of_att_duties_body(s')
    { }

    lemma lem_inv_strictly_increasing_queue_of_att_duties_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state     
    requires inv_strictly_increasing_queue_of_att_duties_body(process)
    ensures inv_strictly_increasing_queue_of_att_duties_body(process')
    {
        
        if pred_curr_att_duty_has_been_decided(process, id)
        {
            var process_mod := f_update_process_after_att_duty_decided(
                                    process,
                                    id,
                                    decided_attestation_data);

            assert inv_strictly_increasing_queue_of_att_duties_body(process_mod);

            var ret_check_for_next_queued_duty := f_check_for_next_queued_duty(process_mod);
            
            lem_inv_strictly_increasing_queue_of_att_duties_f_check_for_next_queued_duty(process_mod, ret_check_for_next_queued_duty.state);

            assert process' == ret_check_for_next_queued_duty.state;
        }
        
    }  

    lemma lem_inv_strictly_increasing_queue_of_att_duties_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_queued_att_duty_is_rcvd_duty_body(process)  
    requires concl_future_att_duty_is_higher_than_queued_att_duty_body(process, attestation_duty)  
    requires inv_strictly_increasing_queue_of_att_duties_body(process)
    ensures inv_strictly_increasing_queue_of_att_duties_body(process')
    {
        var process_mod := f_enqueue_new_att_duty(
                                    process,
                                    attestation_duty
                                );
        
        lem_inv_strictly_increasing_queue_of_att_duties_f_check_for_next_queued_duty(process_mod, process');        
    } 

    lemma lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state    
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_strictly_increasing_queue_of_att_duties_body(process)
    requires inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process)
    ensures inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process')
    {}

    lemma lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state    
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_strictly_increasing_queue_of_att_duties_body(process)
    requires inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process)
    ensures inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process')
    { }  
    
    lemma lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)
    requires inv_queued_att_duty_is_rcvd_duty_body(s)
    requires inv_strictly_increasing_queue_of_att_duties_body(s)
    requires inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(s)
    ensures inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(s')
    { }

    lemma lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires forall queued_duty: AttestationDuty | queued_duty in process.attestation_duties_queue ::
                        attestation_duty.slot < queued_duty.slot     
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_strictly_increasing_queue_of_att_duties_body(process)                        
    requires inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process)
    ensures inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process')
    { } 

    lemma lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state    
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_strictly_increasing_queue_of_att_duties_body(process)
    requires inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process)
    ensures inv_strictly_increasing_queue_of_att_duties_body(process')
    ensures inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process')
    decreases process.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(process)  
        {            
            if first_queued_att_duty_was_decided(process)
            {
                var process_mod := f_dequeue_attestation_duties_queue(process);
                lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_check_for_next_queued_duty(process_mod, process');
            }
            else
            { 
                var next_duty := process.attestation_duties_queue[0];
                var process_mod := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..]
                );     

                assert forall queued_duty: AttestationDuty | 
                            queued_duty in process_mod.attestation_duties_queue ::
                                next_duty.slot <= queued_duty.slot;

                assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process_mod);

                lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_start_next_duty(process_mod, next_duty, process');
            }
        }
        else
        { 
            assert process'.all_rcvd_duties == process.all_rcvd_duties;
        }
    }

    lemma lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_queued_att_duty_is_rcvd_duty_body(process)  
    requires concl_next_att_duty_is_higher_than_latest_served_att_duty_body(process, attestation_duty)  
    requires concl_future_att_duty_is_higher_than_queued_att_duty_body(process, attestation_duty)  
    requires inv_strictly_increasing_queue_of_att_duties_body(process)
    requires inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process)
    requires forall queued_duty: AttestationDuty | queued_duty in process.attestation_duties_queue ::
                        queued_duty.slot < attestation_duty.slot
    ensures inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process')
    {
        var process_mod := f_enqueue_new_att_duty(
                                    process,
                                    attestation_duty
                                );

        if process.latest_attestation_duty.isPresent() 
        {
            assert process_mod.latest_attestation_duty.isPresent();
            assert process.latest_attestation_duty.safe_get()
                        == process_mod.latest_attestation_duty.safe_get();
            assert process.latest_attestation_duty.safe_get().slot < attestation_duty.slot;
            assert process_mod.latest_attestation_duty.safe_get().slot < attestation_duty.slot;
            assert inv_strictly_increasing_queue_of_att_duties_body(process_mod);      
            assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process_mod);      
        }
        else 
        {
            assert !process_mod.latest_attestation_duty.isPresent();
            assert inv_strictly_increasing_queue_of_att_duties_body(process_mod);      
            assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process_mod);      
        }
        
        lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_check_for_next_queued_duty(process_mod, process');        
    } 

    lemma lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state    
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_strictly_increasing_queue_of_att_duties_body(process)
    requires inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process)
    ensures inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process')
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var process :=
                f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                process,
                                block
                            );      

        assert inv_queued_att_duty_is_rcvd_duty_body(process);
        assert inv_strictly_increasing_queue_of_att_duties_body(process);
        assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process);
                    

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

            assert inv_queued_att_duty_is_rcvd_duty_body(process);
            assert inv_strictly_increasing_queue_of_att_duties_body(process);
            assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process);

            lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_check_for_next_queued_duty(process, process');
        }
        else
        {               
            assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process);
        }
    } 

    lemma lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state     
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_strictly_increasing_queue_of_att_duties_body(process)
    requires inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process)
    ensures inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process')
    {
        
        if pred_curr_att_duty_has_been_decided(process, id)
        {
            var process_mod := f_update_process_after_att_duty_decided(
                                    process,
                                    id,
                                    decided_attestation_data);

            assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
            assert inv_strictly_increasing_queue_of_att_duties_body(process_mod);
            assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process_mod);

            var ret_check_for_next_queued_duty := f_check_for_next_queued_duty(process_mod);
            
            lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_check_for_next_queued_duty(process_mod, ret_check_for_next_queued_duty.state);

            assert process' == ret_check_for_next_queued_duty.state;    
        }    
    }  

    lemma lem_inv_no_active_consensus_instance_before_receiving_att_duty_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)    
    requires inv_no_active_consensus_instance_before_receiving_att_duty_body(s)
    ensures inv_no_active_consensus_instance_before_receiving_att_duty_body(s')
    { }

    lemma lem_inv_no_active_consensus_instance_before_receiving_att_duty_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_no_active_consensus_instance_before_receiving_att_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_att_duty_body(process')
    {}

    lemma lem_inv_no_active_consensus_instance_before_receiving_att_duty_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires inv_no_active_consensus_instance_before_receiving_att_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_att_duty_body(process')
    { } 

    lemma lem_inv_no_active_consensus_instance_before_receiving_att_duty_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_no_active_consensus_instance_before_receiving_att_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_att_duty_body(process')
    { } 

    lemma lem_inv_no_active_consensus_instance_before_receiving_att_duty_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state    
    requires inv_no_active_consensus_instance_before_receiving_att_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_att_duty_body(process')
    decreases process.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(process)   
        {            
            if first_queued_att_duty_was_decided(process)
            {
                var process_mod := f_dequeue_attestation_duties_queue(process);
                lem_inv_no_active_consensus_instance_before_receiving_att_duty_f_check_for_next_queued_duty(process_mod, process');
            }
            else
            { 
                var process_mod := f_dequeue_first_queued_att_duty(process);
                assert inv_no_active_consensus_instance_before_receiving_att_duty_body(process_mod);

                lem_inv_no_active_consensus_instance_before_receiving_att_duty_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
            }
        }
        else
        { 
            assert process'.all_rcvd_duties == process.all_rcvd_duties;
        }
    }

    lemma lem_inv_no_active_consensus_instance_before_receiving_att_duty_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_no_active_consensus_instance_before_receiving_att_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_att_duty_body(process')
    {
        
        if pred_curr_att_duty_has_been_decided(process, id)
        {
            var process_mod := f_update_process_after_att_duty_decided(
                                    process,
                                    id,
                                    decided_attestation_data);
    
            assert inv_no_active_consensus_instance_before_receiving_att_duty_body(process_mod);

            var ret_check_for_next_queued_duty := f_check_for_next_queued_duty(process_mod);
            
            lem_inv_no_active_consensus_instance_before_receiving_att_duty_f_check_for_next_queued_duty(process_mod, ret_check_for_next_queued_duty.state);

            assert process' == ret_check_for_next_queued_duty.state;        
        }
    } 
    
    lemma lem_inv_no_active_consensus_instance_before_receiving_att_duty_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_no_active_consensus_instance_before_receiving_att_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_att_duty_body(process')
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var process :=
                f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                process,
                                block
                            );      
        
        assert inv_no_active_consensus_instance_before_receiving_att_duty_body(process);

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
            
            assert inv_no_active_consensus_instance_before_receiving_att_duty_body(process);

            lem_inv_no_active_consensus_instance_before_receiving_att_duty_f_check_for_next_queued_duty(process, process');
        }
        else
        {               
            assert inv_no_active_consensus_instance_before_receiving_att_duty_body(process);
        }
    } 

    lemma lem_inv_no_active_consensus_instance_before_receiving_att_duty_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_no_active_consensus_instance_before_receiving_att_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_att_duty_body(process')
    {
        var process_mod := f_enqueue_new_att_duty(
                                    process,
                                    attestation_duty
                                );
        
        lem_inv_no_active_consensus_instance_before_receiving_att_duty_f_check_for_next_queued_duty(process_mod, process');        
    } 

    lemma lem_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)    
    requires inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(s)
    ensures inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(s')
    { }

    lemma lem_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process)
    ensures inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process')
    {}

    lemma lem_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process)
    ensures inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process')
    { } 

    lemma lem_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_f_check_for_next_queued_duty_helper(
        process: DVCState,
        process': DVCState,
        process_mod: DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state        
    requires inv_strictly_increasing_queue_of_att_duties_body(process)
    requires inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process)
    requires inv_no_active_consensus_instance_before_receiving_att_duty_body(process)
    requires inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process)
    requires && first_queued_att_duty_was_decided_or_ready_to_be_served(process) 
             && !first_queued_att_duty_was_decided(process)
    requires process_mod == f_dequeue_first_queued_att_duty(process)
    ensures inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process')
    {
        forall k: Slot | k in process_mod.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys 
        ensures k < process.attestation_duties_queue[0].slot;
        {
            assert k in process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;
            assert inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process);
            assert k <= process.latest_attestation_duty.safe_get().slot;
            assert process.latest_attestation_duty.safe_get().slot < process.attestation_duties_queue[0].slot;
            assert k < process.attestation_duties_queue[0].slot;
        }
    }
    

    lemma lem_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state        
    requires inv_strictly_increasing_queue_of_att_duties_body(process)
    requires inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process)
    requires inv_no_active_consensus_instance_before_receiving_att_duty_body(process)
    requires inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process)
    ensures inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process')
    decreases process.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(process) 
        {            
            if first_queued_att_duty_was_decided(process)
            {
                var process_mod := f_dequeue_attestation_duties_queue(process);

                assert inv_strictly_increasing_queue_of_att_duties_body(process_mod);
                assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process_mod);
                assert inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process_mod);
            }
            else
            { 
                var process_mod := f_dequeue_first_queued_att_duty(process);

                if process_mod.latest_attestation_duty.isPresent()
                {
                    assert inv_strictly_increasing_queue_of_att_duties_body(process_mod);
                    assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process_mod);
                    assert inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process_mod);

                    assert  process_mod.latest_attestation_duty.isPresent()
                                ==> process_mod.latest_attestation_duty.safe_get().slot < process.attestation_duties_queue[0].slot;

                    assert process_mod.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys 
                                == process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

                    lem_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_f_check_for_next_queued_duty_helper(
                        process,
                        process',
                        process_mod     
                    );
                    lem_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
                }
                else 
                {
                    assert inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process');
                }
            }
        }
        else
        { }
    }

    lemma lem_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process)
    requires ( forall k: Slot | k in process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys ::
                    k < attestation_duty.slot
            )
    ensures inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process')
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

        assert process'.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys 
                    == process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys 
                            + {attestation_duty.slot};
    } 

    lemma lem_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    requires concl_future_att_duty_is_higher_than_rcvd_att_duty_body(process, attestation_duty)
    requires inv_strictly_increasing_queue_of_att_duties_body(process)
    requires inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process)
    requires inv_no_active_consensus_instance_before_receiving_att_duty_body(process)    
    requires inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process)
    ensures inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process')
    {
        var process_mod := f_enqueue_new_att_duty(
                                    process,
                                    attestation_duty
                                );

        assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
        assert inv_latest_served_duty_is_rcvd_duty_body(process_mod);
        assert inv_strictly_increasing_queue_of_att_duties_body(process_mod);                        
        assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process_mod);         
        assert inv_no_active_consensus_instance_before_receiving_att_duty_body(process_mod);         
        assert inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process_mod);
        
        lem_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_f_check_for_next_queued_duty(process_mod, process');        
    } 

    lemma lem_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_strictly_increasing_queue_of_att_duties_body(process)
    requires inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process)
    requires inv_no_active_consensus_instance_before_receiving_att_duty_body(process)
    requires inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process)
    ensures inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process')
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var process_mod :=
                f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                process,
                                block
                            );      
        
        assert inv_strictly_increasing_queue_of_att_duties_body(process_mod);
        assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process_mod);
        assert inv_no_active_consensus_instance_before_receiving_att_duty_body(process_mod);
        assert inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process_mod);

        if process_mod.current_attestation_duty.isPresent() && process_mod.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            var decided_attestation_data := att_consensus_instances_already_decided[process_mod.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(process_mod.attestation_slashing_db, decided_attestation_data);
            var temp_process := process_mod.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    process_mod.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );
            
            assert inv_strictly_increasing_queue_of_att_duties_body(temp_process);
            assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(temp_process);
            assert inv_no_active_consensus_instance_before_receiving_att_duty_body(temp_process);
            assert inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(temp_process);

            lem_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_f_check_for_next_queued_duty(temp_process, process');

            assert inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process');
        }
        else
        {               
            assert inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process_mod);
        }
    } 

    // TODO
    lemma lem_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_strictly_increasing_queue_of_att_duties_body(process)
    requires inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process)
    requires inv_no_active_consensus_instance_before_receiving_att_duty_body(process)
    requires inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process)
    ensures inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process')
    {
        
        if pred_curr_att_duty_has_been_decided(process, id)
        {
            var local_current_attestation_duty := process.current_attestation_duty.safe_get();

            var process_mod := f_update_process_after_att_duty_decided(
                                    process,
                                    id,
                                    decided_attestation_data);

            assert inv_strictly_increasing_queue_of_att_duties_body(process_mod);
            assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process_mod);
            assert inv_no_active_consensus_instance_before_receiving_att_duty_body(process_mod);
            assert inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process_mod);

            var ret_check_for_next_queued_duty: DVCStateAndOuputs := f_check_for_next_queued_duty(process_mod);
            
            lem_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_f_check_for_next_queued_duty(process_mod, ret_check_for_next_queued_duty.state);

            var res := ret_check_for_next_queued_duty.(
                            state := ret_check_for_next_queued_duty.state,
                            outputs := getEmptyOuputs().(
                                            att_shares_sent := multicast(
                                                                    process_mod.attestation_shares_to_broadcast[local_current_attestation_duty.slot], 
                                                                    process.peers)
                                        )          
                        );

            assert process' == res.state;
            assert inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process');
        }
    } 

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)    
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(s)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(s')
    { }

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process')
    { }

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires attestation_duty in process.all_rcvd_duties
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process')
    { } 

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process')
    { } 

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state    
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process')
    decreases process.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(process)    
        {            
            if first_queued_att_duty_was_decided(process)
            {
                var process_mod := f_dequeue_attestation_duties_queue(process);

                assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
                lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_f_check_for_next_queued_duty(process_mod, process');
            }
            else
            { 
                var process_mod := f_dequeue_first_queued_att_duty(process);
                assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process_mod);

                lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
            }
        }
        else
        { 
            assert process'.all_rcvd_duties == process.all_rcvd_duties;
        }
    }

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process')
    {
        
        if pred_curr_att_duty_has_been_decided(process, id)
        {
            var local_current_attestation_duty := process.current_attestation_duty.safe_get();

            var process_mod := f_update_process_after_att_duty_decided(
                                    process,
                                    id,
                                    decided_attestation_data);

            assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
            assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process_mod);

            var ret_dvc := f_check_for_next_queued_duty(process_mod).state;
            lem_inv_queued_att_duty_is_rcvd_duty_f_check_for_next_queued_duty(process_mod, ret_dvc);
            assert inv_queued_att_duty_is_rcvd_duty_body(ret_dvc);
            
            lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_f_check_for_next_queued_duty(process_mod, ret_dvc);
            assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(ret_dvc);

            assert process' == ret_dvc;        
        }
    }

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process')
    {
        var process_mod := f_enqueue_new_att_duty(
                                    process,
                                    attestation_duty
                                );

        assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
        assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process_mod);
        
        lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_f_check_for_next_queued_duty(process_mod, process');        
    }

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process')
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var process :=
                f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                process,
                                block
                            );      
        
        assert inv_queued_att_duty_is_rcvd_duty_body(process);
        assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process);

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
            
            assert inv_queued_att_duty_is_rcvd_duty_body(process);
            assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process);

            lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_f_check_for_next_queued_duty(process, process');
        }
        else
        {               
            assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process);
        }
    } 

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)    
    requires inv_consensus_instances_only_for_rcvd_duties_body(s)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(s')
    { }

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    { }

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires attestation_duty in process.all_rcvd_duties
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    { } 

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    { } 

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_f_check_for_next_queued_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state    
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    decreases process.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(process)    
        {            
            if first_queued_att_duty_was_decided(process)
            {
                var process_mod := f_dequeue_attestation_duties_queue(process);
                assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
                lem_inv_consensus_instances_only_for_rcvd_duties_f_check_for_next_queued_duty(process_mod, process');
            }
            else
            { 
                var process_mod := f_dequeue_first_queued_att_duty(process);
                assert inv_consensus_instances_only_for_rcvd_duties_body(process_mod);

                lem_inv_consensus_instances_only_for_rcvd_duties_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
            }
        }
        else
        { 
            assert process'.all_rcvd_duties == process.all_rcvd_duties;
        }
    }

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    {
        
        if pred_curr_att_duty_has_been_decided(process, id)
        {
            var local_current_attestation_duty := process.current_attestation_duty.safe_get();

            var process_mod := f_update_process_after_att_duty_decided(
                                    process,
                                    id,
                                    decided_attestation_data);

            assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
            assert inv_consensus_instances_only_for_rcvd_duties_body(process_mod);

            var ret_dvc := f_check_for_next_queued_duty(process_mod).state;
            lem_inv_queued_att_duty_is_rcvd_duty_f_check_for_next_queued_duty(process_mod, ret_dvc);
            assert inv_queued_att_duty_is_rcvd_duty_body(ret_dvc);
            
            lem_inv_consensus_instances_only_for_rcvd_duties_f_check_for_next_queued_duty(process_mod, ret_dvc);
            assert inv_consensus_instances_only_for_rcvd_duties_body(ret_dvc);

            assert process' == ret_dvc;   
        }     
    }

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    {
        var process_mod := f_enqueue_new_att_duty(
                                    process,
                                    attestation_duty
                                );

        assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
        assert inv_consensus_instances_only_for_rcvd_duties_body(process_mod);
        
        lem_inv_consensus_instances_only_for_rcvd_duties_f_check_for_next_queued_duty(process_mod, process');        
    }

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_queued_att_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var process :=
                f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                process,
                                block
                            );      
        
        assert inv_queued_att_duty_is_rcvd_duty_body(process);
        assert inv_consensus_instances_only_for_rcvd_duties_body(process);

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
            
            assert inv_queued_att_duty_is_rcvd_duty_body(process);
            assert inv_consensus_instances_only_for_rcvd_duties_body(process);

            lem_inv_consensus_instances_only_for_rcvd_duties_f_check_for_next_queued_duty(process, process');
        }
        else
        {               
            assert inv_consensus_instances_only_for_rcvd_duties_body(process);
        }
    } 

    
}