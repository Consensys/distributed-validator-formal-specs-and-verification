include "../../../../common/commons.dfy"
include "../../common/block_proposer_instrumented.dfy"
include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_attestation_creation.dfy"
include "../inv.dfy"
include "../../../common/helper_sets_lemmas.dfy"
include "../../common/common_proofs.dfy"
include "../../common/block_dvc_spec_axioms.dfy"

include "../../../common/helper_pred_fcn.dfy"


module Fnc_Invs_1
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Spec
    import opened DV
    import opened Block_Inv_With_Empty_Initial_Block_Slashing_DB
    import opened Helper_Sets_Lemmas
    import opened Common_Proofs
    import opened DVC_Spec_Axioms
    import opened Helper_Pred_Fcn

    
    lemma lem_updated_all_rcvd_duties_f_serve_attestation_duty(
        dvc: DVCState,
        attestation_duty: AttestationDuty,
        dvc': DVCState
    )  
    requires f_serve_attestation_duty.requires(dvc, attestation_duty)
    requires dvc' == f_serve_attestation_duty(dvc, attestation_duty).state
    ensures dvc'.all_rcvd_duties == dvc.all_rcvd_duties + {attestation_duty}    
    { }

    lemma lem_updated_all_rcvd_duties_f_check_for_next_duty(
        dvc: DVCState,
        attestation_duty: AttestationDuty, 
        dvc': DVCState
    )
    requires f_check_for_next_duty.requires(dvc, attestation_duty)
    requires dvc' == f_check_for_next_duty(dvc, attestation_duty).state
    ensures dvc'.all_rcvd_duties == dvc.all_rcvd_duties
    { }

    lemma lem_updated_all_rcvd_duties_f_start_next_duty(
        dvc: DVCState, 
        attestation_duty: AttestationDuty, 
        dvc': DVCState)
    requires f_start_next_duty.requires(dvc, attestation_duty)
    requires dvc' == f_start_next_duty(dvc, attestation_duty).state
    ensures dvc'.all_rcvd_duties == dvc.all_rcvd_duties        
    { }  

    lemma lem_updated_all_rcvd_duties_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state 
    ensures process'.all_rcvd_duties == process.all_rcvd_duties
    { }  


    lemma lem_updated_all_rcvd_duties_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    ensures process.all_rcvd_duties == process'.all_rcvd_duties
    {}

    lemma lem_updated_all_rcvd_duties_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    ensures process.all_rcvd_duties == process'.all_rcvd_duties
    { }   

    lemma lem_updated_all_rcvd_duties_f_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)
    requires s.all_rcvd_duties == s'.all_rcvd_duties
    { } 

    lemma lem_updated_all_rcvd_duties_f_resend_attestation_share(
        s: DVCState,
        s': DVCState 
    )
    requires f_resend_attestation_share.requires(s)
    requires s' == f_resend_attestation_share(s).state
    requires s.all_rcvd_duties == s'.all_rcvd_duties
    { } 

    // // lemma lem_inv_queued_att_duty_is_rcvd_duty_add_block_to_bn(
    // //     s: DVCState,
    // //     block: BeaconBlock,
    // //     s': DVCState 
    // // )
    // // requires f_add_block_to_bn.requires(s, block)
    // // requires s' == f_add_block_to_bn(s, block)
    // // requires inv_queued_att_duty_is_rcvd_duty_body(s)
    // // ensures inv_queued_att_duty_is_rcvd_duty_body(s')
    // // { } 
    
    // // lemma lem_inv_queued_att_duty_is_rcvd_duty_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    // // requires f_start_next_duty.requires(process, attestation_duty)
    // // requires process' == f_start_next_duty(process, attestation_duty).state
    // // requires inv_queued_att_duty_is_rcvd_duty_body(process)
    // // ensures inv_queued_att_duty_is_rcvd_duty_body(process')
    // // { }  

    // // lemma lem_inv_queued_att_duty_is_rcvd_duty_f_check_for_next_duty(
    // //     process: DVCState,
    // //     process': DVCState
    // // )
    // // requires f_check_for_next_duty.requires(process, attestation_duty)
    // // requires process' == f_check_for_next_duty(process).state
    // // requires inv_queued_att_duty_is_rcvd_duty_body(process)
    // // ensures inv_queued_att_duty_is_rcvd_duty_body(process')
    // // 
    // // {
    // //     if first_queued_att_duty_was_decided_or_ready_to_be_served(process)
    // //     {            
    // //         if first_queued_att_duty_was_decided(process)
    // //         {
    // //             var process_mod := f_dequeue_attestation_duties_queue(process);
    // //             lem_inv_queued_att_duty_is_rcvd_duty_f_check_for_next_duty(process_mod, process');
    // //         }
    // //         else
    // //         { 
    // //             var process_mod := process.(
    // //                 attestation_duties_queue := process.attestation_duties_queue[1..]
    // //             );         
    // //             lem_inv_queued_att_duty_is_rcvd_duty_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
    // //         }
    // //     }
    // //     else
    // //     { 
    // //         assert process'.all_rcvd_duties == process.all_rcvd_duties;
    // //     }
    // // }

    // // lemma lem_inv_queued_att_duty_is_rcvd_duty_f_serve_attestation_duty(
    // //     process: DVCState,
    // //     attestation_duty: AttestationDuty,
    // //     process': DVCState
    // // )  
    // // requires f_serve_attestation_duty.requires(process, attestation_duty)
    // // requires process' == f_serve_attestation_duty(process, attestation_duty).state
    // // requires inv_queued_att_duty_is_rcvd_duty_body(process)
    // // ensures inv_queued_att_duty_is_rcvd_duty_body(process')
    // // {
    // //     var process_mod := f_enqueue_new_att_duty(
    // //                                 process,
    // //                                 attestation_duty
    // //                             );

    // //     assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);

    // //     lem_inv_queued_att_duty_is_rcvd_duty_f_check_for_next_duty(process_mod, process');        
    // // }    

    // // lemma lem_inv_queued_att_duty_is_rcvd_duty_f_att_consensus_decided(
    // //     process: DVCState,
    // //     id: Slot,
    // //     decided_attestation_data: AttestationData, 
    // //     process': DVCState
    // // )
    // // requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    // // requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state 
    // // requires inv_queued_att_duty_is_rcvd_duty_body(process)
    // // ensures inv_queued_att_duty_is_rcvd_duty_body(process')
    // // {
        
    // //     if  pred_curr_att_duty_has_been_decided(process, id)
    // //     {
    // //         var process_mod := f_update_process_after_att_duty_decided(
    // //                             process,
    // //                             id,
    // //                             decided_attestation_data);

    // //         assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);

    // //         var ret_check_for_next_queued_duty := f_check_for_next_duty(process_mod);
            
    // //         lem_inv_queued_att_duty_is_rcvd_duty_f_check_for_next_duty(process_mod, ret_check_for_next_queued_duty.state);

    // //         assert process' == ret_check_for_next_queued_duty.state;
    // //     }
    // // }  

    // // lemma lem_inv_queued_att_duty_is_rcvd_duty_f_listen_for_attestation_shares(
    // //     process: DVCState,
    // //     attestation_share: AttestationShare,
    // //     process': DVCState
    // // )
    // // requires f_listen_for_attestation_shares.requires(process, attestation_share)
    // // requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    // // requires inv_queued_att_duty_is_rcvd_duty_body(process)
    // // ensures inv_queued_att_duty_is_rcvd_duty_body(process')
    // // {}

    // // lemma lem_inv_queued_att_duty_is_rcvd_duty_f_listen_for_new_imported_blocks(
    // //     process: DVCState,
    // //     block: BeaconBlock,
    // //     process': DVCState
    // // )
    // // requires f_listen_for_new_imported_blocks.requires(process, block)
    // // requires process' == f_listen_for_new_imported_blocks(process, block).state
    // // requires inv_queued_att_duty_is_rcvd_duty_body(process)
    // // ensures inv_queued_att_duty_is_rcvd_duty_body(process')
    // // {
    // //     var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

    // //     var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

    // //     var process :=
    // //             f_stopConsensusInstances_after_receiving_new_imported_blocks(
    // //                             process,
    // //                             block
    // //                         );      

    // //     assert inv_queued_att_duty_is_rcvd_duty_body(process);
                    

    // //     if pred_listen_for_new_imported_blocks_checker(process, att_consensus_instances_already_decided)
    // //     {
    // //         var process := f_updateConsensusInstanceValidityCheck_in_listen_for_new_imported_blocks(
    // //                                 process,
    // //                                 att_consensus_instances_already_decided
    // //                             );

    // //         assert inv_queued_att_duty_is_rcvd_duty_body(process);

    // //         lem_inv_queued_att_duty_is_rcvd_duty_f_check_for_next_duty(process, process');
    // //     }
    // //     else
    // //     {
    // //         assert inv_queued_att_duty_is_rcvd_duty_body(process);
    // //     }
    // // }  

    lemma lem_inv_current_att_duty_is_rcvd_duty_f_start_next_duty(
        process: DVCState, 
        attestation_duty: AttestationDuty, 
        process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state    
    requires attestation_duty in process.all_rcvd_duties
    requires inv_current_att_duty_is_rcvd_duty_body(process)
    ensures inv_current_att_duty_is_rcvd_duty_body(process')
    { }  

    lemma lem_inv_current_att_duty_is_rcvd_duty_f_check_for_next_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state
    requires attestation_duty in process.all_rcvd_duties
    requires inv_current_att_duty_is_rcvd_duty_body(process)
    ensures inv_current_att_duty_is_rcvd_duty_body(process')
    { }

    lemma lem_inv_current_att_duty_is_rcvd_duty_f_terminate_current_attestation_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_current_att_duty_is_rcvd_duty_body(process)
    ensures inv_current_att_duty_is_rcvd_duty_body(process')
    { }

    lemma lem_inv_current_att_duty_is_rcvd_duty_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_current_att_duty_is_rcvd_duty_body(process)
    ensures inv_current_att_duty_is_rcvd_duty_body(process')
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        lem_inv_current_att_duty_is_rcvd_duty_f_terminate_current_attestation_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_current_att_duty_is_rcvd_duty_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );   
    } 

    lemma lem_inv_current_att_duty_is_rcvd_duty_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state 
    requires inv_current_att_duty_is_rcvd_duty_body(process)
    ensures inv_current_att_duty_is_rcvd_duty_body(process')
    { }  

    lemma lem_inv_current_att_duty_is_rcvd_duty_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_current_att_duty_is_rcvd_duty_body(process)
    ensures inv_current_att_duty_is_rcvd_duty_body(process')
    { }

    lemma lem_inv_current_att_duty_is_rcvd_duty_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_current_att_duty_is_rcvd_duty_body(process)
    ensures inv_current_att_duty_is_rcvd_duty_body(process')
    { }  

    lemma lem_inv_latest_served_duty_is_rcvd_duty_f_start_next_duty(
        process: DVCState, 
        attestation_duty: AttestationDuty, 
        process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state    
    requires attestation_duty in process.all_rcvd_duties
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    { }  

    lemma lem_inv_latest_served_duty_is_rcvd_duty_f_check_for_next_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state
    requires attestation_duty in process.all_rcvd_duties
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    { }

    lemma lem_inv_latest_served_duty_is_rcvd_duty_f_terminate_current_attestation_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    { }

    lemma lem_inv_latest_served_duty_is_rcvd_duty_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        lem_inv_latest_served_duty_is_rcvd_duty_f_terminate_current_attestation_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_latest_served_duty_is_rcvd_duty_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );   
    } 

    lemma lem_inv_latest_served_duty_is_rcvd_duty_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state 
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    { }  

    lemma lem_inv_latest_served_duty_is_rcvd_duty_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    { }

    lemma lem_inv_latest_served_duty_is_rcvd_duty_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    { }

    lemma lem_inv_none_latest_served_duty_implies_none_current_att_duty_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state        
    requires inv_none_latest_served_duty_implies_none_current_att_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_att_duty_body(process')
    { }  

    lemma lem_inv_none_latest_served_duty_implies_none_current_att_duty_f_check_for_next_duty(
        process: DVCState,
        attestation_duty: AttestationDuty, 
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state    
    requires inv_none_latest_served_duty_implies_none_current_att_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_att_duty_body(process')
    { }

    lemma lem_inv_none_latest_served_duty_implies_none_current_att_duty_f_terminate_current_attestation_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_none_latest_served_duty_implies_none_current_att_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_att_duty_body(process')
    { }

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
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        lem_inv_none_latest_served_duty_implies_none_current_att_duty_f_terminate_current_attestation_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_none_latest_served_duty_implies_none_current_att_duty_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );       
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
    { }  

    lemma lem_inv_none_latest_served_duty_implies_none_current_att_duty_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_none_latest_served_duty_implies_none_current_att_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_att_duty_body(process')
    { }

    lemma lem_inv_none_latest_served_duty_implies_none_current_att_duty_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state    
    requires inv_none_latest_served_duty_implies_none_current_att_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_att_duty_body(process')
    { }  

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
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)
    requires inv_none_latest_served_duty_implies_none_current_att_duty_body(s)
    ensures inv_none_latest_served_duty_implies_none_current_att_duty_body(s')
    { }    

    lemma lem_inv_current_att_duty_is_either_none_or_latest_served_duty_f_start_next_duty(
        process: DVCState, 
        attestation_duty: AttestationDuty, 
        process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state        
    requires inv_current_att_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_att_duty_is_either_none_or_latest_served_duty_body(process')
    { }  

    lemma lem_inv_current_att_duty_is_either_none_or_latest_served_duty_f_check_for_next_duty(
        process: DVCState,
        attestation_duty: AttestationDuty, 
        process': DVCState
    )
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state    
    requires inv_current_att_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_att_duty_is_either_none_or_latest_served_duty_body(process')
    { }

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
    { } 

    lemma lem_inv_current_att_duty_is_either_none_or_latest_served_duty_f_terminate_current_attestation_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_current_att_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_att_duty_is_either_none_or_latest_served_duty_body(process')
    { }

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
    { }  

    lemma lem_inv_current_att_duty_is_either_none_or_latest_served_duty_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_current_att_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_att_duty_is_either_none_or_latest_served_duty_body(process')
    { }

    lemma lem_inv_current_att_duty_is_either_none_or_latest_served_duty_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state    
    requires inv_current_att_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_att_duty_is_either_none_or_latest_served_duty_body(process')
    { }  

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
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)
    requires inv_current_att_duty_is_either_none_or_latest_served_duty_body(s)
    ensures inv_current_att_duty_is_either_none_or_latest_served_duty_body(s')
    { }

    lemma lem_inv_available_current_att_duty_is_latest_served_att_duty_f_start_next_duty(
        process: DVCState, 
        attestation_duty: AttestationDuty, 
        process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state        
    requires inv_available_current_att_duty_is_latest_served_att_duty_body(process)
    ensures inv_available_current_att_duty_is_latest_served_att_duty_body(process')
    { }  

    lemma lem_inv_available_current_att_duty_is_latest_served_att_duty_f_check_for_next_duty(
        process: DVCState,
        attestation_duty: AttestationDuty, 
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state    
    requires inv_available_current_att_duty_is_latest_served_att_duty_body(process)
    ensures inv_available_current_att_duty_is_latest_served_att_duty_body(process')
    { }

    lemma lem_inv_available_current_att_duty_is_latest_served_att_duty_f_terminate_current_attestation_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_available_current_att_duty_is_latest_served_att_duty_body(process)
    ensures inv_available_current_att_duty_is_latest_served_att_duty_body(process')
    { }

    lemma lem_inv_available_current_att_duty_is_latest_served_att_duty_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_none_latest_served_duty_implies_none_current_att_duty_body(process)  
    requires inv_available_current_att_duty_is_latest_served_att_duty_body(process)
    ensures inv_available_current_att_duty_is_latest_served_att_duty_body(process')
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        lem_inv_available_current_att_duty_is_latest_served_att_duty_f_terminate_current_attestation_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_available_current_att_duty_is_latest_served_att_duty_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );         
    } 

    lemma lem_inv_available_current_att_duty_is_latest_served_att_duty_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state     
    requires inv_available_current_att_duty_is_latest_served_att_duty_body(process)
    ensures inv_available_current_att_duty_is_latest_served_att_duty_body(process')
    { }  

    lemma lem_inv_available_current_att_duty_is_latest_served_att_duty_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_available_current_att_duty_is_latest_served_att_duty_body(process)
    ensures inv_available_current_att_duty_is_latest_served_att_duty_body(process')
    { }

    lemma lem_inv_available_current_att_duty_is_latest_served_att_duty_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state    
    requires inv_available_current_att_duty_is_latest_served_att_duty_body(process)
    ensures inv_available_current_att_duty_is_latest_served_att_duty_body(process')
    { }  

    lemma lem_inv_available_current_att_duty_is_latest_served_att_duty_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state    
    requires inv_available_current_att_duty_is_latest_served_att_duty_body(process)
    ensures inv_available_current_att_duty_is_latest_served_att_duty_body(process')
    { }       
         
    lemma lem_inv_available_current_att_duty_is_latest_served_att_duty_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)
    requires inv_available_current_att_duty_is_latest_served_att_duty_body(s)
    ensures inv_available_current_att_duty_is_latest_served_att_duty_body(s')
    { }

    // // lemma lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    // // requires f_start_next_duty.requires(process, attestation_duty)
    // // requires process' == f_start_next_duty(process, attestation_duty).state        
    // // requires inv_none_latest_served_duty_implies_none_current_att_duty_body(process) || inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process)
    // // ensures inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process')
    // // { }  

    // // lemma lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_check_for_next_duty(
    // //     process: DVCState,
    // //     process': DVCState
    // // )
    // // requires f_check_for_next_duty.requires(process, attestation_duty)
    // // requires process' == f_check_for_next_duty(process, attestation_duty).state    
    // // requires inv_none_latest_served_duty_implies_none_current_att_duty_body(process) || inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process)
    // // ensures inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process')
    // // 
    // // {
    // //     if first_queued_att_duty_was_decided_or_ready_to_be_served(process)    
    // //     {            
    // //         if first_queued_att_duty_was_decided(process)
    // //         {
    // //             var process_mod := f_dequeue_attestation_duties_queue(process);
    // //             lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_check_for_next_duty(process_mod, process');
    // //         }
    // //         else
    // //         { 
    // //             var process_mod := process.(
    // //                 attestation_duties_queue := process.attestation_duties_queue[1..]
    // //             );     
    // //             assert inv_none_latest_served_duty_implies_none_current_att_duty_body(process_mod) || inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process_mod);

    // //             lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
    // //         }
    // //     }
    // //     else
    // //     { 
    // //         assert process'.all_rcvd_duties == process.all_rcvd_duties;
    // //     }
    // // }

    // // lemma lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_serve_attestation_duty(
    // //     process: DVCState,
    // //     attestation_duty: AttestationDuty,
    // //     process': DVCState
    // // )  
    // // requires f_serve_attestation_duty.requires(process, attestation_duty)
    // // requires process' == f_serve_attestation_duty(process, attestation_duty).state
    // // requires inv_none_latest_served_duty_implies_none_current_att_duty_body(process)  
    // // requires inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process)
    // // ensures inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process')
    // // {
    // //     var process_mod := f_enqueue_new_att_duty(
    // //                                 process,
    // //                                 attestation_duty
    // //                             );
        
    // //     lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_check_for_next_duty(process_mod, process');        
    // // } 

    // // lemma lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_att_consensus_decided(
    // //     process: DVCState,
    // //     id: Slot,
    // //     decided_attestation_data: AttestationData, 
    // //     process': DVCState
    // // )
    // // requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    // // requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state     
    // // requires inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process)
    // // ensures inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process')
    // // {
        
    // //     if pred_curr_att_duty_has_been_decided(process, id)
    // //     {
    // //         var process_mod := f_update_process_after_att_duty_decided(
    // //                                 process,
    // //                                 id,
    // //                                 decided_attestation_data);

    // //         assert inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process_mod);

    // //         var ret_check_for_next_queued_duty := f_check_for_next_duty(process_mod);
            
    // //         lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_check_for_next_duty(process_mod, ret_check_for_next_queued_duty.state);

    // //         assert process' == ret_check_for_next_queued_duty.state;
    // //     }
        
    // // }  

    // // lemma lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_listen_for_attestation_shares(
    // //     process: DVCState,
    // //     attestation_share: AttestationShare,
    // //     process': DVCState
    // // )
    // // requires f_listen_for_attestation_shares.requires(process, attestation_share)
    // // requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    // // requires inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process)
    // // ensures inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process')
    // // {}

    // // lemma lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_listen_for_new_imported_blocks(
    // //     process: DVCState,
    // //     block: BeaconBlock,
    // //     process': DVCState
    // // )
    // // requires f_listen_for_new_imported_blocks.requires(process, block)
    // // requires process' == f_listen_for_new_imported_blocks(process, block).state    
    // // requires inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process)
    // // ensures inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process')
    // // {
    // //     var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

    // //     var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

    // //     var process :=
    // //             f_stopConsensusInstances_after_receiving_new_imported_blocks(
    // //                             process,
    // //                             block
    // //                         );      

    // //     assert inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process);
                    

    // //     if pred_listen_for_new_imported_blocks_checker(process, att_consensus_instances_already_decided)
    // //     {
    // //         var process := f_updateConsensusInstanceValidityCheck_in_listen_for_new_imported_blocks(
    // //                                 process,
    // //                                 att_consensus_instances_already_decided
    // //                             );
            
    // //         assert inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process);

    // //         lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_check_for_next_duty(process, process');
    // //     }
    // //     else
    // //     {   
    // //         assert inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process);
    // //     }
    // // }  

    // // lemma lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_resend_attestation_share(
    // //     process: DVCState,
    // //     process': DVCState)
    // // requires f_resend_attestation_share.requires(process)
    // // requires process' == f_resend_attestation_share(process).state    
    // // requires inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process)
    // // ensures inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(process')
    // // { }       
         
    // // lemma lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_add_block_to_bn(
    // //     s: DVCState,
    // //     block: BeaconBlock,
    // //     s': DVCState 
    // // )
    // // requires f_add_block_to_bn.requires(s, block)
    // // requires s' == f_add_block_to_bn(s, block)
    // // requires inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(s)
    // // ensures inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(s')
    // // { }

    // // lemma lem_inv_strictly_increasing_queue_of_att_duties_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    // // requires f_start_next_duty.requires(process, attestation_duty)
    // // requires process' == f_start_next_duty(process, attestation_duty).state        
    // // requires inv_strictly_increasing_queue_of_att_duties_body(process)
    // // ensures inv_strictly_increasing_queue_of_att_duties_body(process')
    // // { }  

    // // lemma lem_inv_strictly_increasing_queue_of_att_duties_f_check_for_next_duty(
    // //     process: DVCState,
    // //     process': DVCState
    // // )
    // // requires f_check_for_next_duty.requires(process, attestation_duty)
    // // requires process' == f_check_for_next_duty(process, attestation_duty).state    
    // // requires inv_strictly_increasing_queue_of_att_duties_body(process)
    // // ensures inv_strictly_increasing_queue_of_att_duties_body(process')
    // // 
    // // {
    // //     if first_queued_att_duty_was_decided_or_ready_to_be_served(process)    
    // //     {            
    // //         if first_queued_att_duty_was_decided(process)
    // //         {
    // //             var process_mod := f_dequeue_attestation_duties_queue(process);
    // //             lem_inv_strictly_increasing_queue_of_att_duties_f_check_for_next_duty(process_mod, process');
    // //         }
    // //         else
    // //         { 
    // //             var process_mod := process.(
    // //                 attestation_duties_queue := process.attestation_duties_queue[1..]
    // //             );     
    // //             assert inv_none_latest_served_duty_implies_none_current_att_duty_body(process_mod) || inv_strictly_increasing_queue_of_att_duties_body(process_mod);

    // //             lem_inv_strictly_increasing_queue_of_att_duties_f_start_next_duty(process_mod, process.attestation_duties_queue[0], process');
    // //         }
    // //     }
    // //     else
    // //     { 
    // //         assert process'.all_rcvd_duties == process.all_rcvd_duties;
    // //     }
    // // }

    // // lemma lem_inv_strictly_increasing_queue_of_att_duties_f_listen_for_attestation_shares(
    // //     process: DVCState,
    // //     attestation_share: AttestationShare,
    // //     process': DVCState
    // // )
    // // requires f_listen_for_attestation_shares.requires(process, attestation_share)
    // // requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    // // requires inv_strictly_increasing_queue_of_att_duties_body(process)
    // // ensures inv_strictly_increasing_queue_of_att_duties_body(process')
    // // {}

    // // lemma lem_inv_strictly_increasing_queue_of_att_duties_f_listen_for_new_imported_blocks(
    // //     process: DVCState,
    // //     block: BeaconBlock,
    // //     process': DVCState
    // // )
    // // requires f_listen_for_new_imported_blocks.requires(process, block)
    // // requires process' == f_listen_for_new_imported_blocks(process, block).state    
    // // requires inv_strictly_increasing_queue_of_att_duties_body(process)
    // // ensures inv_strictly_increasing_queue_of_att_duties_body(process')
    // // {
    // //     var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

    // //     var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

    // //     var process :=
    // //             f_stopConsensusInstances_after_receiving_new_imported_blocks(
    // //                             process,
    // //                             block
    // //                         );      

    // //     assert inv_strictly_increasing_queue_of_att_duties_body(process);
                    

    // //     if pred_listen_for_new_imported_blocks_checker(process, att_consensus_instances_already_decided)
    // //     {
    // //         var process := f_updateConsensusInstanceValidityCheck_in_listen_for_new_imported_blocks(
    // //                                 process,
    // //                                 att_consensus_instances_already_decided
    // //                             );
            
    // //         assert inv_strictly_increasing_queue_of_att_duties_body(process);

    // //         lem_inv_strictly_increasing_queue_of_att_duties_f_check_for_next_duty(process, process');
    // //     }
    // //     else
    // //     {   
    // //         assert inv_strictly_increasing_queue_of_att_duties_body(process);
    // //     }
    // // }  

    // // lemma lem_inv_strictly_increasing_queue_of_att_duties_f_resend_attestation_share(
    // //     process: DVCState,
    // //     process': DVCState)
    // // requires f_resend_attestation_share.requires(process)
    // // requires process' == f_resend_attestation_share(process).state    
    // // requires inv_strictly_increasing_queue_of_att_duties_body(process)
    // // ensures inv_strictly_increasing_queue_of_att_duties_body(process')
    // // { }       
         
    // // lemma lem_inv_strictly_increasing_queue_of_att_duties_add_block_to_bn(
    // //     s: DVCState,
    // //     block: BeaconBlock,
    // //     s': DVCState 
    // // )
    // // requires f_add_block_to_bn.requires(s, block)
    // // requires s' == f_add_block_to_bn(s, block)
    // // requires inv_strictly_increasing_queue_of_att_duties_body(s)
    // // ensures inv_strictly_increasing_queue_of_att_duties_body(s')
    // // { }

    // // lemma lem_inv_strictly_increasing_queue_of_att_duties_f_att_consensus_decided(
    // //     process: DVCState,
    // //     id: Slot,
    // //     decided_attestation_data: AttestationData, 
    // //     process': DVCState
    // // )
    // // requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    // // requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state     
    // // requires inv_strictly_increasing_queue_of_att_duties_body(process)
    // // ensures inv_strictly_increasing_queue_of_att_duties_body(process')
    // // {
        
    // //     if pred_curr_att_duty_has_been_decided(process, id)
    // //     {
    // //         var process_mod := f_update_process_after_att_duty_decided(
    // //                                 process,
    // //                                 id,
    // //                                 decided_attestation_data);

    // //         assert inv_strictly_increasing_queue_of_att_duties_body(process_mod);

    // //         var ret_check_for_next_queued_duty := f_check_for_next_duty(process_mod);
            
    // //         lem_inv_strictly_increasing_queue_of_att_duties_f_check_for_next_duty(process_mod, ret_check_for_next_queued_duty.state);

    // //         assert process' == ret_check_for_next_queued_duty.state;
    // //     }
        
    // // }  

    // // lemma lem_inv_strictly_increasing_queue_of_att_duties_f_serve_attestation_duty(
    // //     process: DVCState,
    // //     attestation_duty: AttestationDuty,
    // //     process': DVCState
    // // )  
    // // requires f_serve_attestation_duty.requires(process, attestation_duty)
    // // requires process' == f_serve_attestation_duty(process, attestation_duty).state
    // // requires inv_queued_att_duty_is_rcvd_duty_body(process)  
    // // requires concl_future_att_duty_is_higher_than_queued_att_duty_body(process, attestation_duty)  
    // // requires inv_strictly_increasing_queue_of_att_duties_body(process)
    // // ensures inv_strictly_increasing_queue_of_att_duties_body(process')
    // // {
    // //     var process_mod := f_enqueue_new_att_duty(
    // //                                 process,
    // //                                 attestation_duty
    // //                             );
        
    // //     lem_inv_strictly_increasing_queue_of_att_duties_f_check_for_next_duty(process_mod, process');        
    // // } 

    // // lemma lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_listen_for_attestation_shares(
    // //     process: DVCState,
    // //     attestation_share: AttestationShare,
    // //     process': DVCState
    // // )
    // // requires f_listen_for_attestation_shares.requires(process, attestation_share)
    // // requires process' == f_listen_for_attestation_shares(process, attestation_share).state    
    // // requires inv_queued_att_duty_is_rcvd_duty_body(process)
    // // requires inv_strictly_increasing_queue_of_att_duties_body(process)
    // // requires inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process)
    // // ensures inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process')
    // // {}

    // // lemma lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_resend_attestation_share(
    // //     process: DVCState,
    // //     process': DVCState)
    // // requires f_resend_attestation_share.requires(process)
    // // requires process' == f_resend_attestation_share(process).state    
    // // requires inv_queued_att_duty_is_rcvd_duty_body(process)
    // // requires inv_strictly_increasing_queue_of_att_duties_body(process)
    // // requires inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process)
    // // ensures inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process')
    // // { }  
    
    // // lemma lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_add_block_to_bn(
    // //     s: DVCState,
    // //     block: BeaconBlock,
    // //     s': DVCState 
    // // )
    // // requires f_add_block_to_bn.requires(s, block)
    // // requires s' == f_add_block_to_bn(s, block)
    // // requires inv_queued_att_duty_is_rcvd_duty_body(s)
    // // requires inv_strictly_increasing_queue_of_att_duties_body(s)
    // // requires inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(s)
    // // ensures inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(s')
    // // { }

    // // lemma lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    // // requires f_start_next_duty.requires(process, attestation_duty)
    // // requires process' == f_start_next_duty(process, attestation_duty).state   
    // // requires forall queued_duty: AttestationDuty | queued_duty in process.attestation_duties_queue ::
    // //                     attestation_duty.slot < queued_duty.slot     
    // // requires inv_queued_att_duty_is_rcvd_duty_body(process)
    // // requires inv_strictly_increasing_queue_of_att_duties_body(process)                        
    // // requires inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process)
    // // ensures inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process')
    // // { } 

    // // lemma lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_check_for_next_duty(
    // //     process: DVCState,
    // //     process': DVCState
    // // )
    // // requires f_check_for_next_duty.requires(process, attestation_duty)
    // // requires process' == f_check_for_next_duty(process, attestation_duty).state    
    // // requires inv_queued_att_duty_is_rcvd_duty_body(process)
    // // requires inv_strictly_increasing_queue_of_att_duties_body(process)
    // // requires inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process)
    // // ensures inv_strictly_increasing_queue_of_att_duties_body(process')
    // // ensures inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process')
    // // 
    // // {
    // //     if first_queued_att_duty_was_decided_or_ready_to_be_served(process)  
    // //     {            
    // //         if first_queued_att_duty_was_decided(process)
    // //         {
    // //             var process_mod := f_dequeue_attestation_duties_queue(process);
    // //             lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_check_for_next_duty(process_mod, process');
    // //         }
    // //         else
    // //         { 
    // //             var next_duty := process.attestation_duties_queue[0];
    // //             var process_mod := process.(
    // //                 attestation_duties_queue := process.attestation_duties_queue[1..]
    // //             );     

    // //             assert forall queued_duty: AttestationDuty | 
    // //                         queued_duty in process_mod.attestation_duties_queue ::
    // //                             next_duty.slot <= queued_duty.slot;

    // //             assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process_mod);

    // //             lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_start_next_duty(process_mod, next_duty, process');
    // //         }
    // //     }
    // //     else
    // //     { 
    // //         assert process'.all_rcvd_duties == process.all_rcvd_duties;
    // //     }
    // // }

    // // lemma lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_serve_attestation_duty(
    // //     process: DVCState,
    // //     attestation_duty: AttestationDuty,
    // //     process': DVCState
    // // )  
    // // requires f_serve_attestation_duty.requires(process, attestation_duty)
    // // requires process' == f_serve_attestation_duty(process, attestation_duty).state
    // // requires inv_queued_att_duty_is_rcvd_duty_body(process)  
    // // requires inv_att_duty_in_next_delivery_is_not_lower_than_latest_served_att_duty_body(process, attestation_duty)  
    // // requires concl_future_att_duty_is_higher_than_queued_att_duty_body(process, attestation_duty)  
    // // requires inv_strictly_increasing_queue_of_att_duties_body(process)
    // // requires inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process)
    // // requires forall queued_duty: AttestationDuty | queued_duty in process.attestation_duties_queue ::
    // //                     queued_duty.slot < attestation_duty.slot
    // // ensures inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process')
    // // {
    // //     var process_mod := f_enqueue_new_att_duty(
    // //                                 process,
    // //                                 attestation_duty
    // //                             );

    // //     if process.latest_attestation_duty.isPresent() 
    // //     {
    // //         assert process_mod.latest_attestation_duty.isPresent();
    // //         assert process.latest_attestation_duty.safe_get()
    // //                     == process_mod.latest_attestation_duty.safe_get();
    // //         assert process.latest_attestation_duty.safe_get().slot < attestation_duty.slot;
    // //         assert process_mod.latest_attestation_duty.safe_get().slot < attestation_duty.slot;
    // //         assert inv_strictly_increasing_queue_of_att_duties_body(process_mod);      
    // //         assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process_mod);      
    // //     }
    // //     else 
    // //     {
    // //         assert !process_mod.latest_attestation_duty.isPresent();
    // //         assert inv_strictly_increasing_queue_of_att_duties_body(process_mod);      
    // //         assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process_mod);      
    // //     }
        
    // //     lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_check_for_next_duty(process_mod, process');        
    // // } 

    // // lemma lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_listen_for_new_imported_blocks(
    // //     process: DVCState,
    // //     block: BeaconBlock,
    // //     process': DVCState
    // // )
    // // requires f_listen_for_new_imported_blocks.requires(process, block)
    // // requires process' == f_listen_for_new_imported_blocks(process, block).state    
    // // requires inv_queued_att_duty_is_rcvd_duty_body(process)
    // // requires inv_strictly_increasing_queue_of_att_duties_body(process)
    // // requires inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process)
    // // ensures inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process')
    // // {
    // //     var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

    // //     var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

    // //     var process :=
    // //             f_stopConsensusInstances_after_receiving_new_imported_blocks(
    // //                             process,
    // //                             block
    // //                         );      

    // //     assert inv_queued_att_duty_is_rcvd_duty_body(process);
    // //     assert inv_strictly_increasing_queue_of_att_duties_body(process);
    // //     assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process);
                    

    // //     if pred_listen_for_new_imported_blocks_checker(process, att_consensus_instances_already_decided)
    // //     {
    // //         var process := f_updateConsensusInstanceValidityCheck_in_listen_for_new_imported_blocks(
    // //                                 process,
    // //                                 att_consensus_instances_already_decided
    // //                             );
    // //         assert inv_queued_att_duty_is_rcvd_duty_body(process);
    // //         assert inv_strictly_increasing_queue_of_att_duties_body(process);
    // //         assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process);

    // //         lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_check_for_next_duty(process, process');
    // //     }
    // //     else
    // //     {               
    // //         assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process);
    // //     }
    // // } 

    // // lemma lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_att_consensus_decided(
    // //     process: DVCState,
    // //     id: Slot,
    // //     decided_attestation_data: AttestationData, 
    // //     process': DVCState
    // // )
    // // requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    // // requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state     
    // // requires inv_queued_att_duty_is_rcvd_duty_body(process)
    // // requires inv_strictly_increasing_queue_of_att_duties_body(process)
    // // requires inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process)
    // // ensures inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process')
    // // {
        
    // //     if pred_curr_att_duty_has_been_decided(process, id)
    // //     {
    // //         var process_mod := f_update_process_after_att_duty_decided(
    // //                                 process,
    // //                                 id,
    // //                                 decided_attestation_data);

    // //         assert inv_queued_att_duty_is_rcvd_duty_body(process_mod);
    // //         assert inv_strictly_increasing_queue_of_att_duties_body(process_mod);
    // //         assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(process_mod);

    // //         var ret_check_for_next_queued_duty := f_check_for_next_duty(process_mod);
            
    // //         lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_check_for_next_duty(process_mod, ret_check_for_next_queued_duty.state);

    // //         assert process' == ret_check_for_next_queued_duty.state;    
    // //     }    
    // // }  

    lemma lem_inv_no_active_consensus_instance_before_receiving_an_att_duty_body_f_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    requires inv_no_active_consensus_instance_before_receiving_an_att_duty_body(s)
    ensures inv_no_active_consensus_instance_before_receiving_an_att_duty_body(s')
    { }

    lemma lem_inv_no_active_consensus_instance_before_receiving_an_att_duty_body_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_no_active_consensus_instance_before_receiving_an_att_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_an_att_duty_body(process')
    {}

    lemma lem_inv_no_active_consensus_instance_before_receiving_an_att_duty_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires inv_no_active_consensus_instance_before_receiving_an_att_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_an_att_duty_body(process')
    { } 

    lemma lem_inv_no_active_consensus_instance_before_receiving_an_att_duty_body_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_no_active_consensus_instance_before_receiving_an_att_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_an_att_duty_body(process')
    { } 

    lemma lem_inv_no_active_consensus_instance_before_receiving_an_att_duty_body_f_check_for_next_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state    
    requires inv_no_active_consensus_instance_before_receiving_an_att_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_an_att_duty_body(process')
    { }

    lemma lem_inv_no_active_consensus_instance_before_receiving_an_att_duty_body_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_no_active_consensus_instance_before_receiving_an_att_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_an_att_duty_body(process')
    { } 
    
    lemma lem_inv_no_active_consensus_instance_before_receiving_an_att_duty_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_no_active_consensus_instance_before_receiving_an_att_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_an_att_duty_body(process')
    { } 

    lemma lem_inv_no_active_consensus_instance_before_receiving_an_att_duty_body_f_terminate_current_attestation_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_no_active_consensus_instance_before_receiving_an_att_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_an_att_duty_body(process')
    { }

    lemma lem_inv_no_active_consensus_instance_before_receiving_an_att_duty_body_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_no_active_consensus_instance_before_receiving_an_att_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_an_att_duty_body(process')
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        lem_inv_no_active_consensus_instance_before_receiving_an_att_duty_body_f_terminate_current_attestation_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_no_active_consensus_instance_before_receiving_an_att_duty_body_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );         
    } 

    lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body_f_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body(s)
    ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body(s')
    { }

    lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body(process)
    ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body(process')
    { }

    lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body(process)
    ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body(process')
    { } 

    lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body_f_terminate_current_attestation_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body(process)
    ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body(process')
    { }
    
    lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body_f_start_next_duty(
        process: DVCState, 
        attestation_duty: AttestationDuty, 
        process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires inv_no_active_consensus_instance_before_receiving_an_att_duty_body(process)
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    requires inv_att_duty_in_next_delivery_is_not_lower_than_rcvd_att_duties_body(process, attestation_duty)
    requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body(process)
    ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body(process')
    { } 

    lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body_f_check_for_next_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state        
    requires inv_no_active_consensus_instance_before_receiving_an_att_duty_body(process)
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    requires inv_att_duty_in_next_delivery_is_not_lower_than_rcvd_att_duties_body(process, attestation_duty)
    requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body(process)
    ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body(process')
    { }

    

    lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_no_active_consensus_instance_before_receiving_an_att_duty_body(process)   
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    requires inv_att_duty_in_next_delivery_is_not_lower_than_rcvd_att_duties_body(process, attestation_duty)
    requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body(process)
    ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body(process')
    { } 

    lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_no_active_consensus_instance_before_receiving_an_att_duty_body(process)
    requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body(process)
    ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body(process')
    { } 

    lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_no_active_consensus_instance_before_receiving_an_att_duty_body(process)
    requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body(process)
    ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body(process')
    { } 

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body_f_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(s)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(s')
    { }

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process')
    { }

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body_f_start_next_duty(
        process: DVCState, 
        attestation_duty: AttestationDuty, 
        process': DVCState
    )
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

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body_f_check_for_next_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state    
    requires attestation_duty in process.all_rcvd_duties
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process')
    { }

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process')
    { }

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body_f_terminate_current_attestation_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process')
    { }

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process')
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body_f_terminate_current_attestation_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );       
    }

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(process')
    { } 

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    requires inv_consensus_instances_only_for_rcvd_duties_body(s)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(s')
    { }

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        process': DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    { }

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_start_next_duty(process: DVCState, attestation_duty: AttestationDuty, process': DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires attestation_duty in process.all_rcvd_duties
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    { } 

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_resend_attestation_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    { } 

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_check_for_next_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state    
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    requires attestation_duty in process.all_rcvd_duties
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    { }

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    { }

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    { }

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    { } 

    
}