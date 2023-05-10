include "../../../../common/commons.dfy"
include "../../common/dvc_attestation_creation_instrumented.dfy"
include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_attestation_creation.dfy"
include "../inv.dfy"
include "../../../common/helper_sets_lemmas.dfy"
include "../../common/common_proofs.dfy"
include "../../../bn_axioms.dfy"
include "../../../rs_axioms.dfy"

include "../../../common/att_helper_pred_fcn.dfy"


module Fnc_Invs_1
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened Att_DVC_Spec
    import opened Att_DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Helper_Sets_Lemmas
    import opened Common_Proofs
    import opened BN_Axioms
    import opened RS_Axioms
    import opened Att_Helper_Pred_Fcn

    
    lemma lem_updated_all_rcvd_duties_f_serve_attestation_duty(
        dvc: Att_DVCState,
        attestation_duty: AttestationDuty,
        dvc': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(dvc, attestation_duty)
    requires dvc' == f_serve_attestation_duty(dvc, attestation_duty).state
    ensures dvc'.all_rcvd_duties == dvc.all_rcvd_duties + {attestation_duty}    
    { }

    lemma lem_updated_all_rcvd_duties_f_check_for_next_duty(
        dvc: Att_DVCState,
        attestation_duty: AttestationDuty, 
        dvc': Att_DVCState
    )
    requires f_check_for_next_duty.requires(dvc, attestation_duty)
    requires dvc' == f_check_for_next_duty(dvc, attestation_duty).state
    ensures dvc'.all_rcvd_duties == dvc.all_rcvd_duties
    { }

    lemma lem_updated_all_rcvd_duties_f_start_next_duty(
        dvc: Att_DVCState, 
        attestation_duty: AttestationDuty, 
        dvc': Att_DVCState)
    requires f_start_next_duty.requires(dvc, attestation_duty)
    requires dvc' == f_start_next_duty(dvc, attestation_duty).state
    ensures dvc'.all_rcvd_duties == dvc.all_rcvd_duties        
    { }  

    lemma lem_updated_all_rcvd_duties_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state 
    ensures process'.all_rcvd_duties == process.all_rcvd_duties
    { }  


    lemma lem_updated_all_rcvd_duties_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    ensures process.all_rcvd_duties == process'.all_rcvd_duties
    {}

    lemma lem_updated_all_rcvd_duties_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    ensures process.all_rcvd_duties == process'.all_rcvd_duties
    { }   

    lemma lem_updated_all_rcvd_duties_f_add_block_to_bn(
        s: Att_DVCState,
        block: BeaconBlock,
        s': Att_DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)
    requires s.all_rcvd_duties == s'.all_rcvd_duties
    { } 

    lemma lem_updated_all_rcvd_duties_f_resend_attestation_share(
        s: Att_DVCState,
        s': Att_DVCState 
    )
    requires f_resend_attestation_share.requires(s)
    requires s' == f_resend_attestation_share(s).state
    requires s.all_rcvd_duties == s'.all_rcvd_duties
    { } 

    lemma lem_inv_current_att_duty_is_rcvd_duty_f_start_next_duty(
        process: Att_DVCState, 
        attestation_duty: AttestationDuty, 
        process': Att_DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state    
    requires attestation_duty in process.all_rcvd_duties
    requires inv_current_att_duty_is_rcvd_duty_body(process)
    ensures inv_current_att_duty_is_rcvd_duty_body(process')
    { }  

    lemma lem_inv_current_att_duty_is_rcvd_duty_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state
    requires attestation_duty in process.all_rcvd_duties
    requires inv_current_att_duty_is_rcvd_duty_body(process)
    ensures inv_current_att_duty_is_rcvd_duty_body(process')
    { }

    lemma lem_inv_current_att_duty_is_rcvd_duty_f_terminate_current_attestation_duty(
        process: Att_DVCState,
        process': Att_DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_current_att_duty_is_rcvd_duty_body(process)
    ensures inv_current_att_duty_is_rcvd_duty_body(process')
    { }

    lemma lem_inv_current_att_duty_is_rcvd_duty_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
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
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state 
    requires inv_current_att_duty_is_rcvd_duty_body(process)
    ensures inv_current_att_duty_is_rcvd_duty_body(process')
    { }  

    lemma lem_inv_current_att_duty_is_rcvd_duty_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_current_att_duty_is_rcvd_duty_body(process)
    ensures inv_current_att_duty_is_rcvd_duty_body(process')
    { }

    lemma lem_inv_current_att_duty_is_rcvd_duty_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_current_att_duty_is_rcvd_duty_body(process)
    ensures inv_current_att_duty_is_rcvd_duty_body(process')
    { }  

    lemma lem_inv_latest_att_duty_is_rcvd_duty_f_start_next_duty(
        process: Att_DVCState, 
        attestation_duty: AttestationDuty, 
        process': Att_DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state    
    requires attestation_duty in process.all_rcvd_duties
    requires inv_latest_att_duty_is_rcvd_duty_body(process)
    ensures inv_latest_att_duty_is_rcvd_duty_body(process')
    { }  

    lemma lem_inv_latest_att_duty_is_rcvd_duty_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state
    requires attestation_duty in process.all_rcvd_duties
    requires inv_latest_att_duty_is_rcvd_duty_body(process)
    ensures inv_latest_att_duty_is_rcvd_duty_body(process')
    { }

    lemma lem_inv_latest_att_duty_is_rcvd_duty_f_terminate_current_attestation_duty(
        process: Att_DVCState,
        process': Att_DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_latest_att_duty_is_rcvd_duty_body(process)
    ensures inv_latest_att_duty_is_rcvd_duty_body(process')
    { }

    lemma lem_inv_latest_att_duty_is_rcvd_duty_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_latest_att_duty_is_rcvd_duty_body(process)
    ensures inv_latest_att_duty_is_rcvd_duty_body(process')
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        lem_inv_latest_att_duty_is_rcvd_duty_f_terminate_current_attestation_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_latest_att_duty_is_rcvd_duty_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );   
    } 

    lemma lem_inv_latest_att_duty_is_rcvd_duty_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state 
    requires inv_latest_att_duty_is_rcvd_duty_body(process)
    ensures inv_latest_att_duty_is_rcvd_duty_body(process')
    { }  

    lemma lem_inv_latest_att_duty_is_rcvd_duty_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_latest_att_duty_is_rcvd_duty_body(process)
    ensures inv_latest_att_duty_is_rcvd_duty_body(process')
    { }

    lemma lem_inv_latest_att_duty_is_rcvd_duty_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_latest_att_duty_is_rcvd_duty_body(process)
    ensures inv_latest_att_duty_is_rcvd_duty_body(process')
    { }

    lemma lem_inv_none_latest_att_duty_implies_none_current_att_duty_f_start_next_duty(process: Att_DVCState, attestation_duty: AttestationDuty, process': Att_DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state        
    requires inv_none_latest_att_duty_implies_none_current_att_duty_body(process)
    ensures inv_none_latest_att_duty_implies_none_current_att_duty_body(process')
    { }  

    lemma lem_inv_none_latest_att_duty_implies_none_current_att_duty_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty, 
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state    
    requires inv_none_latest_att_duty_implies_none_current_att_duty_body(process)
    ensures inv_none_latest_att_duty_implies_none_current_att_duty_body(process')
    { }

    lemma lem_inv_none_latest_att_duty_implies_none_current_att_duty_f_terminate_current_attestation_duty(
        process: Att_DVCState,
        process': Att_DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_none_latest_att_duty_implies_none_current_att_duty_body(process)
    ensures inv_none_latest_att_duty_implies_none_current_att_duty_body(process')
    { }

    lemma lem_inv_none_latest_att_duty_implies_none_current_att_duty_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_none_latest_att_duty_implies_none_current_att_duty_body(process)
    ensures inv_none_latest_att_duty_implies_none_current_att_duty_body(process')
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        lem_inv_none_latest_att_duty_implies_none_current_att_duty_f_terminate_current_attestation_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_none_latest_att_duty_implies_none_current_att_duty_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );       
    } 

    lemma lem_inv_none_latest_att_duty_implies_none_current_att_duty_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state     
    requires inv_none_latest_att_duty_implies_none_current_att_duty_body(process)
    ensures inv_none_latest_att_duty_implies_none_current_att_duty_body(process')
    { }  

    lemma lem_inv_none_latest_att_duty_implies_none_current_att_duty_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_none_latest_att_duty_implies_none_current_att_duty_body(process)
    ensures inv_none_latest_att_duty_implies_none_current_att_duty_body(process')
    { }

    lemma lem_inv_none_latest_att_duty_implies_none_current_att_duty_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state    
    requires inv_none_latest_att_duty_implies_none_current_att_duty_body(process)
    ensures inv_none_latest_att_duty_implies_none_current_att_duty_body(process')
    { }  

    lemma lem_inv_none_latest_att_duty_implies_none_current_att_duty_f_resend_attestation_share(
        process: Att_DVCState,
        process': Att_DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state    
    requires inv_none_latest_att_duty_implies_none_current_att_duty_body(process)
    ensures inv_none_latest_att_duty_implies_none_current_att_duty_body(process')
    { }       
         
    lemma lem_inv_none_latest_att_duty_implies_none_current_att_duty_add_block_to_bn(
        s: Att_DVCState,
        block: BeaconBlock,
        s': Att_DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)
    requires inv_none_latest_att_duty_implies_none_current_att_duty_body(s)
    ensures inv_none_latest_att_duty_implies_none_current_att_duty_body(s')
    { }    

    lemma lem_inv_current_att_duty_is_either_none_or_latest_att_duty_f_start_next_duty(
        process: Att_DVCState, 
        attestation_duty: AttestationDuty, 
        process': Att_DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state        
    requires inv_current_att_duty_is_either_none_or_latest_att_duty_body(process)
    ensures inv_current_att_duty_is_either_none_or_latest_att_duty_body(process')
    { }  

    lemma lem_inv_current_att_duty_is_either_none_or_latest_att_duty_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty, 
        process': Att_DVCState
    )
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state    
    requires inv_current_att_duty_is_either_none_or_latest_att_duty_body(process)
    ensures inv_current_att_duty_is_either_none_or_latest_att_duty_body(process')
    { }

    lemma lem_inv_current_att_duty_is_either_none_or_latest_att_duty_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_none_latest_att_duty_implies_none_current_att_duty_body(process)  
    requires inv_current_att_duty_is_either_none_or_latest_att_duty_body(process)
    ensures inv_current_att_duty_is_either_none_or_latest_att_duty_body(process')
    { } 

    lemma lem_inv_current_att_duty_is_either_none_or_latest_att_duty_f_terminate_current_attestation_duty(
        process: Att_DVCState,
        process': Att_DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_current_att_duty_is_either_none_or_latest_att_duty_body(process)
    ensures inv_current_att_duty_is_either_none_or_latest_att_duty_body(process')
    { }

    lemma lem_inv_current_att_duty_is_either_none_or_latest_att_duty_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state     
    requires inv_current_att_duty_is_either_none_or_latest_att_duty_body(process)
    ensures inv_current_att_duty_is_either_none_or_latest_att_duty_body(process')
    { }  

    lemma lem_inv_current_att_duty_is_either_none_or_latest_att_duty_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_current_att_duty_is_either_none_or_latest_att_duty_body(process)
    ensures inv_current_att_duty_is_either_none_or_latest_att_duty_body(process')
    { }

    lemma lem_inv_current_att_duty_is_either_none_or_latest_att_duty_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state    
    requires inv_current_att_duty_is_either_none_or_latest_att_duty_body(process)
    ensures inv_current_att_duty_is_either_none_or_latest_att_duty_body(process')
    { }  

    lemma lem_inv_current_att_duty_is_either_none_or_latest_att_duty_f_resend_attestation_share(
        process: Att_DVCState,
        process': Att_DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state    
    requires inv_current_att_duty_is_either_none_or_latest_att_duty_body(process)
    ensures inv_current_att_duty_is_either_none_or_latest_att_duty_body(process')
    { }       
         
    lemma lem_inv_current_att_duty_is_either_none_or_latest_att_duty_add_block_to_bn(
        s: Att_DVCState,
        block: BeaconBlock,
        s': Att_DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)
    requires inv_current_att_duty_is_either_none_or_latest_att_duty_body(s)
    ensures inv_current_att_duty_is_either_none_or_latest_att_duty_body(s')
    { }

    lemma lem_inv_available_current_att_duty_is_latest_att_duty_f_start_next_duty(
        process: Att_DVCState, 
        attestation_duty: AttestationDuty, 
        process': Att_DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state        
    requires inv_available_current_att_duty_is_latest_att_duty_body(process)
    ensures inv_available_current_att_duty_is_latest_att_duty_body(process')
    { }  

    lemma lem_inv_available_current_att_duty_is_latest_att_duty_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty, 
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state    
    requires inv_available_current_att_duty_is_latest_att_duty_body(process)
    ensures inv_available_current_att_duty_is_latest_att_duty_body(process')
    { }

    lemma lem_inv_available_current_att_duty_is_latest_att_duty_f_terminate_current_attestation_duty(
        process: Att_DVCState,
        process': Att_DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_available_current_att_duty_is_latest_att_duty_body(process)
    ensures inv_available_current_att_duty_is_latest_att_duty_body(process')
    { }

    lemma lem_inv_available_current_att_duty_is_latest_att_duty_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_none_latest_att_duty_implies_none_current_att_duty_body(process)  
    requires inv_available_current_att_duty_is_latest_att_duty_body(process)
    ensures inv_available_current_att_duty_is_latest_att_duty_body(process')
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        lem_inv_available_current_att_duty_is_latest_att_duty_f_terminate_current_attestation_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_available_current_att_duty_is_latest_att_duty_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );         
    } 

    lemma lem_inv_available_current_att_duty_is_latest_att_duty_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state     
    requires inv_available_current_att_duty_is_latest_att_duty_body(process)
    ensures inv_available_current_att_duty_is_latest_att_duty_body(process')
    { }  

    lemma lem_inv_available_current_att_duty_is_latest_att_duty_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_available_current_att_duty_is_latest_att_duty_body(process)
    ensures inv_available_current_att_duty_is_latest_att_duty_body(process')
    { }

    lemma lem_inv_available_current_att_duty_is_latest_att_duty_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state    
    requires inv_available_current_att_duty_is_latest_att_duty_body(process)
    ensures inv_available_current_att_duty_is_latest_att_duty_body(process')
    { }  

    lemma lem_inv_available_current_att_duty_is_latest_att_duty_f_resend_attestation_share(
        process: Att_DVCState,
        process': Att_DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state    
    requires inv_available_current_att_duty_is_latest_att_duty_body(process)
    ensures inv_available_current_att_duty_is_latest_att_duty_body(process')
    { }       
         
    lemma lem_inv_available_current_att_duty_is_latest_att_duty_add_block_to_bn(
        s: Att_DVCState,
        block: BeaconBlock,
        s': Att_DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)
    requires inv_available_current_att_duty_is_latest_att_duty_body(s)
    ensures inv_available_current_att_duty_is_latest_att_duty_body(s')
    { }

    lemma lem_inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body_f_add_block_to_bn(
        s: Att_DVCState,
        block: BeaconBlock,
        s': Att_DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    requires inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(s)
    ensures inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(s')
    { }

    lemma lem_inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(process)
    ensures inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(process')
    {}

    lemma lem_inv_no_active_consensus_instances_before_the_first_att_duty_was_received_f_start_next_duty(process: Att_DVCState, attestation_duty: AttestationDuty, process': Att_DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(process)
    ensures inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(process')
    { } 

    lemma lem_inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body_f_resend_attestation_share(
        process: Att_DVCState,
        process': Att_DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(process)
    ensures inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(process')
    { } 

    lemma lem_inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state    
    requires inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(process)
    ensures inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(process')
    { }

    lemma lem_inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(process)
    ensures inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(process')
    { } 
    
    lemma lem_inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(process)
    ensures inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(process')
    { } 

    lemma lem_inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body_f_terminate_current_attestation_duty(
        process: Att_DVCState,
        process': Att_DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(process)
    ensures inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(process')
    { }

    lemma lem_inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(process)
    ensures inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(process')
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        lem_inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body_f_terminate_current_attestation_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );         
    } 

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body_f_add_block_to_bn(
        s: Att_DVCState,
        block: BeaconBlock,
        s': Att_DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(s)
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(s')
    { }

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(process)
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(process')
    { }

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body_f_resend_attestation_share(
        process: Att_DVCState,
        process': Att_DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(process)
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(process')
    { } 

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body_f_terminate_current_attestation_duty(
        process: Att_DVCState,
        process': Att_DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(process)
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(process')
    { }
    
    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body_f_start_next_duty(
        process: Att_DVCState, 
        attestation_duty: AttestationDuty, 
        process': Att_DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(process)
    requires inv_latest_att_duty_is_rcvd_duty_body(process)
    requires inv_an_att_duty_in_the_next_delivery_is_not_lower_than_rcvd_att_duties_body(process, attestation_duty)
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(process)
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(process')
    { } 

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state        
    requires inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(process)
    requires inv_latest_att_duty_is_rcvd_duty_body(process)
    requires inv_an_att_duty_in_the_next_delivery_is_not_lower_than_rcvd_att_duties_body(process, attestation_duty)
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(process)
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(process')
    { }

    

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(process)   
    requires inv_latest_att_duty_is_rcvd_duty_body(process)
    requires inv_an_att_duty_in_the_next_delivery_is_not_lower_than_rcvd_att_duties_body(process, attestation_duty)
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(process)
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(process')
    { } 

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(process)
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(process)
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(process')
    { } 

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(process)
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(process)
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(process')
    { } 

    lemma lem_inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body_f_add_block_to_bn(
        s: Att_DVCState,
        block: BeaconBlock,
        s': Att_DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    requires inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(s)
    ensures inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(s')
    { }

    lemma lem_inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process)
    ensures inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process')
    { }

    lemma lem_inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body_f_start_next_duty(
        process: Att_DVCState, 
        attestation_duty: AttestationDuty, 
        process': Att_DVCState
    )
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires attestation_duty in process.all_rcvd_duties
    requires inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process)
    ensures inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process')
    { } 

    lemma lem_inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_f_resend_attestation_share(
        process: Att_DVCState,
        process': Att_DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process)
    ensures inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process')
    { } 

    lemma lem_inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state    
    requires attestation_duty in process.all_rcvd_duties
    requires inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process)
    ensures inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process')
    { }

    lemma lem_inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process)
    ensures inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process')
    { }

    lemma lem_inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body_f_terminate_current_attestation_duty(
        process: Att_DVCState,
        process': Att_DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process)
    ensures inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process')
    { }

    lemma lem_inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process)
    ensures inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process')
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        lem_inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body_f_terminate_current_attestation_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );       
    }

    lemma lem_inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process)
    ensures inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process')
    { } 

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body_f_add_block_to_bn(
        s: Att_DVCState,
        block: BeaconBlock,
        s': Att_DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(s)
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(s')
    { }

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process)
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process')
    { }

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body_f_start_next_duty(process: Att_DVCState, attestation_duty: AttestationDuty, process': Att_DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires attestation_duty in process.all_rcvd_duties
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process)
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process')
    { } 

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body_f_resend_attestation_share(
        process: Att_DVCState,
        process': Att_DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process)
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process')
    { } 

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state    
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process)
    requires attestation_duty in process.all_rcvd_duties
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process')
    { }

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process)
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process')
    { }

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process)
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process')
    { }

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process)
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process')
    { } 

    
}