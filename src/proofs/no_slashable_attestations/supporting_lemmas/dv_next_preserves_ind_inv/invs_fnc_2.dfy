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

include "../../../common/att_helper_pred_fcn.dfy"


module Fnc_Invs_2
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened Att_DVC_Spec
    import opened Att_DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Att_Helper_Sets_Lemmas
    import opened Common_Proofs
    import opened Fnc_Invs_1
    import opened Att_DVC_Spec_Axioms
    import opened Helper_Pred_Fcn

    lemma lem_inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body_f_add_block_to_bn(
        s: Att_DVCState,
        block: BeaconBlock,
        s': Att_DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    requires inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(s)
    ensures inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(s')
    { }

    lemma lem_inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(process)
    ensures inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(process')
    { }

    lemma lem_inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body_f_start_next_duty(
        process: Att_DVCState, 
        attestation_duty: AttestationDuty, 
        process': Att_DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires attestation_duty in process.all_rcvd_duties
    requires inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(process)
    ensures inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(process')
    { } 

    lemma lem_inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body_f_resend_attestation_share(
        process: Att_DVCState,
        process': Att_DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(process)
    ensures inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(process')
    { } 

    lemma lem_inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state    
    requires inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process)
    requires attestation_duty in process.all_rcvd_duties
    requires inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(process)
    ensures inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(process')
    { 
        if attestation_duty.slot in process.future_att_consensus_instances_already_decided.Keys 
        {
        }
        else
        {
            lem_inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body_f_start_next_duty(
                process, 
                attestation_duty, 
                process'
            );
        }
    }

    lemma lem_inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process)
    requires inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(process)
    ensures inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(process')
    { }

    lemma lem_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body_f_terminate_current_attestation_duty(
        process: Att_DVCState,
        process': Att_DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(process)
    ensures inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(process')
    { }

    lemma lem_inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process)
    requires inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(process)
    ensures inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(process')
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        lem_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body_f_terminate_current_attestation_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );           
    }

    lemma lem_inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process)
    requires inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(process)
    ensures inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(process')
    { }  

    
    lemma lem_inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body_f_add_block_to_bn(
        s: Att_DVCState,
        block: BeaconBlock,
        s': Att_DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    requires inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body(s)
    ensures inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body(s')
    { }

    lemma lem_inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body(process)
    ensures inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body(process')
    { }

    lemma lem_inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body_f_start_next_duty(process: Att_DVCState, attestation_duty: AttestationDuty, process': Att_DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires attestation_duty in process.all_rcvd_duties
    requires inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body(process)
    ensures inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body(process')
    { } 

    lemma lem_inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body_f_resend_attestation_share(
        process: Att_DVCState,
        process': Att_DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body(process)
    ensures inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body(process')
    { } 

    lemma lem_inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty, 
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state    
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process)
    requires inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body(process)
    ensures inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body(process')
    { }

    lemma lem_inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process)
    requires inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body(process)
    ensures inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body(process')
    { }

    lemma lem_inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body_f_terminate_current_attestation_duty(
        process: Att_DVCState,
        process': Att_DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body(process)
    ensures inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body(process')
    { }

    lemma lem_inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process)
    requires inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body(process)
    ensures inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body(process')
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        lem_inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body_f_terminate_current_attestation_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );         
    }

    lemma lem_inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process)
    requires inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body(process)
    ensures inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body(process')
    { } 

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body_f_add_block_to_bn(
        s: Att_DVCState,
        block: BeaconBlock,
        s': Att_DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(s)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(s')
    { }

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process')
    { }

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body_f_start_next_duty(process: Att_DVCState, attestation_duty: AttestationDuty, process': Att_DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires attestation_duty in process.all_rcvd_duties
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process')
    { } 

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body_f_resend_attestation_share(
        process: Att_DVCState,
        process': Att_DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process')
    { } 

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state    
    requires inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process)
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process')
    { }

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process)
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process')
    { }

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body_f_terminate_current_attestation_duty(
        process: Att_DVCState,
        process': Att_DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process')
    { }

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process)
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process')
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        lem_inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body_f_terminate_current_attestation_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );           
    }

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(process)
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(process')
    { }   

    lemma lem_inv_monotonic_att_slashing_db_body_f_add_block_to_bn(
        s: Att_DVCState,
        block: BeaconBlock,
        s': Att_DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    ensures inv_monotonic_att_slashing_db_body(s, s') 
    { }

    lemma lem_inv_monotonic_att_slashing_db_body_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    ensures inv_monotonic_att_slashing_db_body(process, process')
    { }

    lemma lem_inv_monotonic_att_slashing_db_body_f_start_next_duty(process: Att_DVCState, attestation_duty: AttestationDuty, process': Att_DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state       
    ensures inv_monotonic_att_slashing_db_body(process, process')
    { } 

    lemma lem_inv_monotonic_att_slashing_db_body_f_resend_attestation_share(
        process: Att_DVCState,
        process': Att_DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    ensures inv_monotonic_att_slashing_db_body(process, process')    
    { } 


    lemma lem_inv_monotonic_att_slashing_db_body_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state        
    ensures inv_monotonic_att_slashing_db_body(process, process')
    { }

    lemma lem_inv_monotonic_att_slashing_db_body_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    ensures inv_monotonic_att_slashing_db_body(process, process')
    { }

    lemma lem_inv_monotonic_att_slashing_db_body_f_terminate_current_attestation_duty(
        process: Att_DVCState,
        process': Att_DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    ensures inv_monotonic_att_slashing_db_body(process, process')
    { }

    lemma lem_inv_monotonic_att_slashing_db_body_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    ensures inv_monotonic_att_slashing_db_body(process, process')
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        lem_inv_monotonic_att_slashing_db_body_f_terminate_current_attestation_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_monotonic_att_slashing_db_body_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );        
    }

    lemma lem_inv_monotonic_att_slashing_db_body_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state   
    ensures inv_monotonic_att_slashing_db_body(process, process')
    { } 

    lemma lem_inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_f_add_block_to_bn(
        s: Att_DVCState,
        block: BeaconBlock,
        s': Att_DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    requires inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(s)
    ensures inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(s')
    { }

    lemma lem_inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(process)
    ensures inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(process')
    { }

    lemma lem_inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_f_start_next_duty(
        process: Att_DVCState, 
        attestation_duty: AttestationDuty, 
        process': Att_DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(process)
    ensures inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(process')
    { } 

    lemma lem_inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_f_resend_attestation_share(
        process: Att_DVCState,
        process': Att_DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(process)
    ensures inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(process')
    { } 

    lemma lem_inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_ces_f_check_for_next_duty_known_decision(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        attestation_data: AttestationData
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(process)
    requires pred_decision_of_att_duty_was_known(process, attestation_duty)
    requires attestation_data == process.future_att_consensus_instances_already_decided[attestation_duty.slot]
    ensures && var new_attestation_slashing_db := 
                    f_update_attestation_slashing_db(
                        process.attestation_slashing_db, 
                        attestation_data
                    );
            && inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_ces(
                            process.attestation_consensus_engine_state, 
                            new_attestation_slashing_db)
    {
        var attestation_data := process.future_att_consensus_instances_already_decided[attestation_duty.slot];      
            
        var slashing_db_attestation := SlashingDBAttestation(
                                        source_epoch := attestation_data.source.epoch,
                                        target_epoch := attestation_data.target.epoch,
                                        signing_root := Some(hash_tree_root(attestation_data)));
        
        var new_attestation_slashing_db := 
                f_update_attestation_slashing_db(
                    process.attestation_slashing_db, 
                    attestation_data
                );

        assert new_attestation_slashing_db == process.attestation_slashing_db + {slashing_db_attestation};
        assert process.attestation_slashing_db <= new_attestation_slashing_db;

        
        assert inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_ces(
                            process.attestation_consensus_engine_state, 
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

        assert inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_ces(
                        process.attestation_consensus_engine_state, 
                        new_attestation_slashing_db);
    }

    lemma lem_inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state    
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process)    
    requires inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(process)
    ensures inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(process')
    { 
        if pred_decision_of_att_duty_was_known(process, attestation_duty)
        {
            assert inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_ces(
                            process.attestation_consensus_engine_state, 
                            process.attestation_slashing_db); 

            var attestation_data := process.future_att_consensus_instances_already_decided[attestation_duty.slot];      
            
            var slashing_db_attestation := SlashingDBAttestation(
                                            source_epoch := attestation_data.source.epoch,
                                            target_epoch := attestation_data.target.epoch,
                                            signing_root := Some(hash_tree_root(attestation_data)));

            lem_inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_ces_f_check_for_next_duty_known_decision(
                process,
                attestation_duty,
                attestation_data
            );
        }
        else
        {
            lem_inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_f_start_next_duty(
                process, 
                attestation_duty, 
                process'
            );
        }
    }

    lemma lem_inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_ces_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(process)
    requires is_decided_data_for_current_slot(process, decided_attestation_data, id)
    ensures && var attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);
            && inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_ces(process.attestation_consensus_engine_state, 
                            attestation_slashing_db)
    {
        var local_current_attestation_duty := process.current_attestation_duty.safe_get();
        var attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);
        assert process.attestation_slashing_db <= attestation_slashing_db;
        assert inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_ces(
                            process.attestation_consensus_engine_state, 
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

        assert inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_ces(process.attestation_consensus_engine_state, 
                            attestation_slashing_db);
    }

    lemma lem_inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process)
    requires inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(process)
    ensures inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(process')
    {
        if  is_decided_data_for_current_slot(process, decided_attestation_data, id)
        {
            var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);
           
            var attestation_with_signature_share := f_calc_att_with_sign_share_from_decided_att_data(
                                                        process,
                                                        id,
                                                        decided_attestation_data
                                                    );    

            var new_attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                                                                process.attestation_consensus_engine_state,
                                                                new_attestation_slashing_db
                                                        );
            
            lem_inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_ces_f_att_consensus_decided(
                    process,
                    id,
                    decided_attestation_data
                );

            lem_inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_updateConsensusInstanceValidityCheck(
                                    process.attestation_consensus_engine_state,
                                    new_attestation_slashing_db,
                                    new_attestation_consensus_engine_state
                                    );
        }   
        else
        {
        }  
    }

    lemma lem_inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_f_terminate_current_attestation_duty(
        process: Att_DVCState,
        process': Att_DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(process)
    ensures inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(process')
    { }

    lemma lem_inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process)
    requires inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(process)
    ensures inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(process')
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        lem_inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_f_terminate_current_attestation_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );   
    }

    lemma lem_inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process)
    requires inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(process)
    ensures inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(process')
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var process_after_stopping_consensus_instance :=
                process.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );               
        
        assert inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(process);
        assert inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(process);

        if pred_listen_for_new_imported_blocks_checker(process_after_stopping_consensus_instance, att_consensus_instances_already_decided)
        {
            var decided_attestation_data := att_consensus_instances_already_decided[process_after_stopping_consensus_instance.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(process_after_stopping_consensus_instance.attestation_slashing_db, decided_attestation_data);

            assert process_after_stopping_consensus_instance.attestation_slashing_db <= new_attestation_slashing_db;
            assert inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_ces(process_after_stopping_consensus_instance.attestation_consensus_engine_state, 
                              process.attestation_slashing_db); 

            forall s: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation> |
                            ( && s  in process_after_stopping_consensus_instance.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                              && vp in process_after_stopping_consensus_instance.attestation_consensus_engine_state.att_slashing_db_hist[s]
                              && db in process_after_stopping_consensus_instance.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
                            )   
            ensures db <= new_attestation_slashing_db               
            {
                calc {
                    db; 
                    <=
                    process_after_stopping_consensus_instance.attestation_slashing_db;
                    <=
                    new_attestation_slashing_db;
                }                        
            }
        }
        else
        {               
            assert inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(process);
        }
    }   
    
    lemma lem_inv_monotonic_att_slashing_db_hist_body_f_add_block_to_bn(
        s: Att_DVCState,
        block: BeaconBlock,
        s': Att_DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    ensures inv_monotonic_att_slashing_db_hist_body(s, s')
    { }

    lemma lem_inv_monotonic_att_slashing_db_hist_body_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    ensures inv_monotonic_att_slashing_db_hist_body(process, process')
    { }

    lemma lem_inv_monotonic_att_slashing_db_hist_body_f_start_next_duty(process: Att_DVCState, attestation_duty: AttestationDuty, process': Att_DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state       
    ensures inv_monotonic_att_slashing_db_hist_body(process, process')
    { } 

    lemma lem_inv_monotonic_att_slashing_db_hist_body_f_resend_attestation_share(
        process: Att_DVCState,
        process': Att_DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    ensures inv_monotonic_att_slashing_db_hist_body(process, process')     
    { } 


    lemma lem_inv_monotonic_att_slashing_db_hist_body_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state        
    ensures inv_monotonic_att_slashing_db_hist_body(process, process')
    { }

    lemma lem_inv_monotonic_att_slashing_db_hist_body_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    ensures inv_monotonic_att_slashing_db_hist_body(process, process')
    { }

    lemma lem_inv_monotonic_att_slashing_db_hist_body_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    ensures inv_monotonic_att_slashing_db_hist_body(process, process')
    { }

    lemma lem_inv_monotonic_att_slashing_db_hist_body_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state   
    ensures inv_monotonic_att_slashing_db_hist_body(process, process')    
    { } 

    lemma lem_inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body_f_add_block_to_bn(
        s: Att_DVCState,
        block: BeaconBlock,
        s': Att_DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    requires inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body(s)
    ensures inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body(s')
    { }

    lemma lem_inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body(process)
    ensures inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body(process')   
    { }

    lemma lem_inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body_f_start_next_duty(process: Att_DVCState, attestation_duty: AttestationDuty, process': Att_DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state       
    requires inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body(process)
    ensures inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body(process')   
    { } 

    lemma lem_inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body_f_resend_attestation_share(
        process: Att_DVCState,
        process': Att_DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body(process)
    ensures inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body(process')     
    { } 


    lemma lem_inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state        
    requires inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body(process)
    ensures inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body(process')   
    { }

    lemma lem_inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body(process)
    ensures inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body(process')   
    { }

    lemma lem_inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body(process)
    ensures inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body(process')   
    { }

    lemma lem_inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state   
    requires inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body(process)
    ensures inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body(process')    
    { } 

    lemma lem_inv_rcvd_att_shares_are_from_sent_messages_f_add_block_to_bn(
        s: Att_DVCState,
        block: BeaconBlock,
        s': Att_DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    ensures s'.rcvd_attestation_shares == s.rcvd_attestation_shares 
    { }

    lemma lem_inv_rcvd_att_shares_are_from_sent_messages_f_start_next_duty(process: Att_DVCState, attestation_duty: AttestationDuty, process': Att_DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state       
    ensures process'.rcvd_attestation_shares == process.rcvd_attestation_shares
    { } 

    lemma lem_inv_rcvd_att_shares_are_from_sent_messages_f_resend_attestation_share(
        process: Att_DVCState,
        process': Att_DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    ensures process'.rcvd_attestation_shares == process.rcvd_attestation_shares
    { } 


    lemma lem_inv_rcvd_att_shares_are_from_sent_messages_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state        
    ensures process'.rcvd_attestation_shares == process.rcvd_attestation_shares
    { }

    lemma lem_inv_rcvd_att_shares_are_from_sent_messages_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    ensures process'.rcvd_attestation_shares == process.rcvd_attestation_shares
    { }

    lemma lem_inv_rcvd_att_shares_are_from_sent_messages_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    ensures process'.rcvd_attestation_shares == process.rcvd_attestation_shares
    { }

    lemma lem_inv_rcvd_att_shares_are_from_sent_messages_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
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
    { } 

    lemma lem_multicast_getMessagesFromMessagesWithRecipient(dvc: Att_DVCState, attestation_with_signature_share: AttestationShare)
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
            invariant   checked_mcast_msgs == {}
                        ==> 
                        getMessagesFromMessagesWithRecipient(checked_mcast_msgs) == {}
            invariant   checked_mcast_msgs != {}
                        ==> 
                        getMessagesFromMessagesWithRecipient(checked_mcast_msgs) == { attestation_with_signature_share } 
            decreases |all_mcast_msgs|
        {
            var msg :|  msg in all_mcast_msgs;
            assert msg.message ==  attestation_with_signature_share;
            all_mcast_msgs := all_mcast_msgs - {msg};
            checked_mcast_msgs := checked_mcast_msgs + {msg};
        }        

        assert getMessagesFromMessagesWithRecipient(mcast_msgs) == { attestation_with_signature_share };
    }

    lemma lem_inv_attestation_shares_to_broadcast_are_sent_messages_add_block_to_bn(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    ensures process'.attestation_shares_to_broadcast == process.attestation_shares_to_broadcast
    { }

    lemma lem_inv_attestation_shares_to_broadcast_are_sent_messages_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state       
    ensures process'.attestation_shares_to_broadcast == process.attestation_shares_to_broadcast        
    ensures process'.peers == process.peers          
    { }

    lemma lem_inv_attestation_shares_to_broadcast_are_sent_messages_f_start_next_duty(process: Att_DVCState, attestation_duty: AttestationDuty, process': Att_DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state       
    ensures process'.attestation_shares_to_broadcast == process.attestation_shares_to_broadcast                  
    ensures process'.peers == process.peers
    { } 

    lemma lem_inv_attestation_shares_to_broadcast_are_sent_messages_f_resend_attestation_share(
        process: Att_DVCState,
        process': Att_DVCState)
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    ensures process'.attestation_shares_to_broadcast == process.attestation_shares_to_broadcast                  
    ensures process'.peers == process.peers
    { } 

    lemma lem_inv_attestation_shares_to_broadcast_are_sent_messages_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state        
    ensures process'.attestation_shares_to_broadcast == process.attestation_shares_to_broadcast                  
    ensures process'.peers == process.peers
    { }

    lemma lem_inv_attestation_shares_to_broadcast_are_sent_messages_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState,
        outputs: Outputs
    )
    requires |process.peers| > 0
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires outputs == f_att_consensus_decided(process, id, decided_attestation_data).outputs    
    requires decided_attestation_data.slot == id  
    ensures process'.attestation_shares_to_broadcast.Values <= getMessagesFromMessagesWithRecipient(outputs.att_shares_sent) + process.attestation_shares_to_broadcast.Values
    {   
        if  is_decided_data_for_current_slot(process, decided_attestation_data, id)
        {
            var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);

            var attestation_with_signature_share := f_calc_att_with_sign_share_from_decided_att_data(
                                                        process,
                                                        id,
                                                        decided_attestation_data
                                                    );       
            var process_mod := 
                    f_update_att_slashing_db_and_consensus_engine_after_att_consensus_decided(
                            process,
                            id,
                            decided_attestation_data,
                            attestation_with_signature_share,
                            new_attestation_slashing_db
                        );           

            lem_multicast_getMessagesFromMessagesWithRecipient(process_mod, attestation_with_signature_share);
        }
        else
        {
        }
    }

    lemma lem_inv_attestation_shares_to_broadcast_are_sent_messages_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    ensures process'.attestation_shares_to_broadcast == process.attestation_shares_to_broadcast
    { }

    lemma lem_inv_attestation_shares_to_broadcast_are_sent_messages_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state   
    ensures process'.attestation_shares_to_broadcast.Values <= process.attestation_shares_to_broadcast.Values
    { } 

    lemma lem_inv_rcvd_att_shares_are_from_sent_messages_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
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

            assert && ( k in attestation_shares_db_at_slot.Keys 
                        ==> 
                        new_set == attestation_shares_db_at_slot[k] + {attestation_share}
                      )
                   && ( k !in attestation_shares_db_at_slot.Keys 
                        ==> 
                        new_set == {attestation_share}
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
        }
        else
        {             
            assert process'.rcvd_attestation_shares == process.rcvd_attestation_shares;            
        }
    }

    lemma lem_inv_rcvd_att_shares_are_from_sent_messages_f_listen_for_attestation_shares_domain(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
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

            assert && ( k in attestation_shares_db_at_slot.Keys 
                        ==> 
                        new_set == attestation_shares_db_at_slot[k] + {attestation_share}
                      )
                   && ( k !in attestation_shares_db_at_slot.Keys 
                        ==> 
                        new_set == {attestation_share}
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
        }
        else
        {             
            assert process'.rcvd_attestation_shares == process.rcvd_attestation_shares;            
        }
    }  

    lemma lem_inv_available_latest_att_duty_is_from_dv_seq_of_att_duties_f_add_block_to_bn(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_available_latest_att_duty_is_from_dv_seq_of_att_duties(
                    hn, 
                    process, 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    ensures inv_available_latest_att_duty_is_from_dv_seq_of_att_duties(
                    hn, 
                    process', 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    {
        
    }
    
    lemma lem_inv_available_latest_att_duty_is_from_dv_seq_of_att_duties_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state        
    requires inv_available_latest_att_duty_is_from_dv_seq_of_att_duties(
                    hn, 
                    process, 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    ensures inv_available_latest_att_duty_is_from_dv_seq_of_att_duties(
                    hn, 
                    process', 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    {}

    lemma lem_inv_available_latest_att_duty_is_from_dv_seq_of_att_duties_f_resend_attestation_share(
        process: Att_DVCState,
        process': Att_DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat  
    )
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state        
    requires inv_available_latest_att_duty_is_from_dv_seq_of_att_duties(
                    hn, 
                    process, 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    ensures inv_available_latest_att_duty_is_from_dv_seq_of_att_duties(
                    hn, 
                    process', 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    { } 

    lemma lem_inv_available_latest_att_duty_is_from_dv_seq_of_att_duties_f_start_next_duty(
        process: Att_DVCState, 
        attestation_duty: AttestationDuty, 
        process': Att_DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat         
    )
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state       
    requires pred_exists_an_att_duty_from_dv_seq_of_att_duties_for_a_given_att_duty(  
                    attestation_duty,
                    hn,
                    sequence_attestation_duties_to_be_served,    
                    index_next_attestation_duty_to_be_served
                )       
    requires inv_available_latest_att_duty_is_from_dv_seq_of_att_duties(
                    hn, 
                    process, 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    ensures inv_available_latest_att_duty_is_from_dv_seq_of_att_duties(
                    hn, 
                    process', 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    { } 


    lemma lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState,
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
    requires inv_available_latest_att_duty_is_from_dv_seq_of_att_duties(
                    hn, 
                    process, 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    ensures inv_available_latest_att_duty_is_from_dv_seq_of_att_duties(
                    hn, 
                    process', 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served + 1)
    {
        assert pred_exists_an_att_duty_from_dv_seq_of_att_duties_for_a_given_att_duty(  
                        attestation_duty,
                        hn,
                        sequence_attestation_duties_to_be_served, 
                        index_next_attestation_duty_to_be_served + 1
                    );     
    } 

    lemma lem_inv_available_latest_att_duty_is_from_dv_seq_of_att_duties_f_check_for_next_duty(
        process: Att_DVCState,
        process': Att_DVCState,
        attestation_duty: AttestationDuty,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state    
    requires pred_exists_an_att_duty_from_dv_seq_of_att_duties_for_a_given_att_duty(  
                        attestation_duty,
                        hn,
                        sequence_attestation_duties_to_be_served, 
                        index_next_attestation_duty_to_be_served
                    )
    requires inv_available_latest_att_duty_is_from_dv_seq_of_att_duties(
                    hn, 
                    process, 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served
             )
    ensures inv_available_latest_att_duty_is_from_dv_seq_of_att_duties(
                    hn, 
                    process', 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    {
        if attestation_duty.slot in process.future_att_consensus_instances_already_decided.Keys 
        {
        }
        else
        {
            lem_inv_available_latest_att_duty_is_from_dv_seq_of_att_duties_f_start_next_duty(
                process, 
                attestation_duty, 
                process',
                hn,
                sequence_attestation_duties_to_be_served,    
                index_next_attestation_duty_to_be_served    
            );
        }   
    }

    lemma lem_inv_available_latest_att_duty_is_from_dv_seq_of_att_duties_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires inv_available_latest_att_duty_is_from_dv_seq_of_att_duties(
                    hn, 
                    process, 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served
             )
    ensures inv_available_latest_att_duty_is_from_dv_seq_of_att_duties(
                    hn, 
                    process', 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    { } 

    lemma lem_inv_available_latest_att_duty_is_from_dv_seq_of_att_duties_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_available_latest_att_duty_is_from_dv_seq_of_att_duties(
                    hn, 
                    process, 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served
             )
    ensures inv_available_latest_att_duty_is_from_dv_seq_of_att_duties(
                    hn, 
                    process', 
                    sequence_attestation_duties_to_be_served, 
                    index_next_attestation_duty_to_be_served)
    { } 

    lemma lem_inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body_f_terminate_current_attestation_duty(
        process: Att_DVCState,
        process': Att_DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(
                process, 
                hn, 
                sequence_attestation_duties_to_be_served, 
                index_next_attestation_duty_to_be_served)
    ensures inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(
                process',
                hn, 
                sequence_attestation_duties_to_be_served, 
                index_next_attestation_duty_to_be_served)
    { }

    lemma lem_inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body_f_start_next_duty(
        dvc: Att_DVCState, 
        attestation_duty: AttestationDuty, 
        dvc': Att_DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_start_next_duty.requires(dvc, attestation_duty)
    requires dvc' == f_start_next_duty(dvc, attestation_duty).state
    requires inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(
                dvc, 
                hn, 
                sequence_attestation_duties_to_be_served, 
                index_next_attestation_duty_to_be_served)
    ensures inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(
                dvc',
                hn, 
                sequence_attestation_duties_to_be_served, 
                index_next_attestation_duty_to_be_served)  
    { } 

    lemma lem_inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body_f_check_for_next_duty(
        dvc: Att_DVCState,
        attestation_duty: AttestationDuty, 
        dvc': Att_DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_check_for_next_duty.requires(dvc, attestation_duty)
    requires dvc' == f_check_for_next_duty(dvc, attestation_duty).state
    requires inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(
                dvc, 
                hn, 
                sequence_attestation_duties_to_be_served, 
                index_next_attestation_duty_to_be_served)
    ensures inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(
                dvc',
                hn, 
                sequence_attestation_duties_to_be_served, 
                index_next_attestation_duty_to_be_served)  
    { } 

    lemma lem_inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body_f_serve_attestation_duty(
        dvc: Att_DVCState,
        attestation_duty: AttestationDuty,
        dvc': Att_DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )  
    requires f_serve_attestation_duty.requires(dvc, attestation_duty)
    requires dvc' == f_serve_attestation_duty(dvc, attestation_duty).state
    requires inv_exists_an_att_duty_in_dv_seq_of_att_duties_for_a_given_att_duty(                
                                    attestation_duty, 
                                    hn, 
                                    sequence_attestation_duties_to_be_served,
                                    index_next_attestation_duty_to_be_served
                                );
    requires inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(
                dvc, 
                hn, 
                sequence_attestation_duties_to_be_served, 
                index_next_attestation_duty_to_be_served)
    ensures inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(
                dvc',
                hn, 
                sequence_attestation_duties_to_be_served, 
                index_next_attestation_duty_to_be_served)  
    { }

    lemma lem_inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state 
    requires inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(
                process, 
                hn, 
                sequence_attestation_duties_to_be_served, 
                index_next_attestation_duty_to_be_served)
    ensures inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(
                process',
                hn, 
                sequence_attestation_duties_to_be_served, 
                index_next_attestation_duty_to_be_served)  
    { }  


    lemma lem_inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(
                process, 
                hn, 
                sequence_attestation_duties_to_be_served, 
                index_next_attestation_duty_to_be_served)
    ensures inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(
                process',
                hn, 
                sequence_attestation_duties_to_be_served, 
                index_next_attestation_duty_to_be_served)  
    {}

    lemma lem_inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(
                process, 
                hn, 
                sequence_attestation_duties_to_be_served, 
                index_next_attestation_duty_to_be_served)
    ensures inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(
                process',
                hn, 
                sequence_attestation_duties_to_be_served, 
                index_next_attestation_duty_to_be_served)  
    { }   

    lemma lem_inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body_f_add_block_to_bn(
        s: Att_DVCState,
        block: BeaconBlock,
        s': Att_DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)
    requires inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(
                s, 
                hn, 
                sequence_attestation_duties_to_be_served, 
                index_next_attestation_duty_to_be_served)
    ensures inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(
                s',
                hn, 
                sequence_attestation_duties_to_be_served, 
                index_next_attestation_duty_to_be_served)  
    { } 

    lemma lem_inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body_f_resend_attestation_share(
        s: Att_DVCState,
        s': Att_DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat  
    )
    requires f_resend_attestation_share.requires(s)
    requires s' == f_resend_attestation_share(s).state
    requires inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(
                s, 
                hn, 
                sequence_attestation_duties_to_be_served, 
                index_next_attestation_duty_to_be_served)
    ensures inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(
                s',
                hn, 
                sequence_attestation_duties_to_be_served, 
                index_next_attestation_duty_to_be_served)  
    { } 

    lemma lem_inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_body_f_start_next_duty(
        dvc: Att_DVCState,
        attestation_duty: AttestationDuty,
        dvc': Att_DVCState
    )  
    requires f_start_next_duty.requires(dvc, attestation_duty)
    requires dvc' == f_start_next_duty(dvc, attestation_duty).state
    requires dvc.all_rcvd_duties != {}
    ensures inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_body(dvc')
    { 
        
    }

    lemma lem_inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_body_f_check_for_next_duty(
        dvc: Att_DVCState,
        attestation_duty: AttestationDuty,
        dvc': Att_DVCState
    )  
    requires f_check_for_next_duty.requires(dvc, attestation_duty)
    requires dvc' == f_check_for_next_duty(dvc, attestation_duty).state
    requires dvc.all_rcvd_duties != {}
    ensures inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_body(dvc')
    { 
        if attestation_duty.slot in dvc.future_att_consensus_instances_already_decided.Keys
        {
            assert inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_body(dvc');
        } 
        else
        {
            lem_inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_body_f_start_next_duty(
                dvc,
                attestation_duty,
                dvc'
            );
            assert inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_body(dvc');
        }
    }

    lemma lem_inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_body_f_serve_attestation_duty(
        dvc: Att_DVCState,
        attestation_duty: AttestationDuty,
        dvc': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(dvc, attestation_duty)
    requires dvc' == f_serve_attestation_duty(dvc, attestation_duty).state
    requires inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_body(dvc)
    ensures inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_body(dvc')
    { 
        var process_rcvd_duty := 
                dvc.(all_rcvd_duties := dvc.all_rcvd_duties + {attestation_duty});
        assert process_rcvd_duty.all_rcvd_duties != {};
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        assert process_after_stopping_active_consensus_instance.all_rcvd_duties != {};
        lem_inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_body_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            dvc'
        );  
    }

    lemma lem_inv_no_rcvd_att_duties_are_higher_than_latest_att_duty_body_f_serve_attestation_duty(
        dvc: Att_DVCState,
        attestation_duty: AttestationDuty,
        dvc': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(dvc, attestation_duty)
    requires dvc' == f_serve_attestation_duty(dvc, attestation_duty).state
    requires inv_no_rcvd_att_duties_are_higher_than_latest_att_duty_body(dvc)
    requires inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_body(dvc)
    ensures inv_no_rcvd_att_duties_are_higher_than_latest_att_duty_body(dvc')
    { 
        var process_rcvd_duty := 
                dvc.(all_rcvd_duties := dvc.all_rcvd_duties + { attestation_duty });
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        assert  process_after_stopping_active_consensus_instance.all_rcvd_duties
                ==
                process_rcvd_duty.all_rcvd_duties;
        assert  dvc' 
                == 
                f_check_for_next_duty(
                    process_after_stopping_active_consensus_instance,
                    attestation_duty
                ).state
                ;
        assert  dvc'.all_rcvd_duties
                ==
                process_after_stopping_active_consensus_instance.all_rcvd_duties
                ;
        assert  && dvc'.latest_attestation_duty.isPresent()
                && dvc'.latest_attestation_duty.safe_get() == attestation_duty;

        if !dvc.latest_attestation_duty.isPresent()
        {
            assert  dvc.all_rcvd_duties == {};
            assert  process_rcvd_duty.all_rcvd_duties 
                    ==
                    process_after_stopping_active_consensus_instance.all_rcvd_duties
                    ==
                    { attestation_duty }
                    ==
                    dvc'.all_rcvd_duties;
            assert inv_no_rcvd_att_duties_are_higher_than_latest_att_duty_body(dvc');
        }
        else
        {
            assert dvc.latest_attestation_duty.safe_get().slot < attestation_duty.slot;
        }
    }

    lemma lem_f_construct_aggregated_attestation_for_new_attestation_share_construct_valid_attestations(
        construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>, 
        attestation: Attestation,
        attestation_share: AttestationShare, 
        k: (AttestationData, seq<bool>),
        rcvd_attestation_shares: map<Slot,map<(AttestationData, seq<bool>), set<AttestationShare>>>
    )
    requires construct_signed_attestation_signature_assumptions_helper(
                construct_signed_attestation_signature,
                dv_pubkey,
                all_nodes
             )
    requires attestation_share.data.slot in rcvd_attestation_shares.Keys
    requires k in rcvd_attestation_shares[attestation_share.data.slot]
    requires construct_signed_attestation_signature(rcvd_attestation_shares[attestation_share.data.slot][k]).isPresent()    
    requires all_att_shares_have_the_same_data(rcvd_attestation_shares[attestation_share.data.slot][k], attestation.data)
    requires && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(attestation.data.target.epoch));
             && var attestation_signing_root := compute_attestation_signing_root(attestation.data, fork_version);      
             && signer_threshold(all_nodes, rcvd_attestation_shares[attestation_share.data.slot][k], attestation_signing_root) 
    requires attestation 
             == 
             f_construct_aggregated_attestation_for_new_attestation_share(
                            attestation_share,
                            k, 
                            construct_signed_attestation_signature,
                            rcvd_attestation_shares
                        );
    ensures is_valid_attestation(attestation, dv_pubkey)
    {
        
    }

    lemma lem_inv_outputs_attestations_submited_are_valid_f_start_next_duty(
        process: Att_DVCState, 
        attestation_duty: AttestationDuty, 
        process': Att_DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state    
    ensures inv_outputs_attestations_submited_are_valid(
                f_start_next_duty(process, attestation_duty).outputs,
                process'.dv_pubkey
                )
    { }  

    lemma lem_inv_outputs_attestations_submited_are_valid_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state
    ensures inv_outputs_attestations_submited_are_valid(
                f_check_for_next_duty(process, attestation_duty).outputs,
                process'.dv_pubkey
                )
    { }

    lemma lem_inv_outputs_attestations_submited_are_valid_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    ensures inv_outputs_attestations_submited_are_valid(
                f_serve_attestation_duty(process, attestation_duty).outputs,
                process'.dv_pubkey
                )
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        lem_inv_outputs_attestations_submited_are_valid_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );   
    } 

    lemma lem_inv_outputs_attestations_submited_are_valid_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state 
    ensures inv_outputs_attestations_submited_are_valid(
                f_att_consensus_decided(process, id, decided_attestation_data).outputs,
                process'.dv_pubkey
                )
    { }  

    lemma lem_inv_outputs_attestations_submited_are_valid_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires construct_signed_attestation_signature_assumptions_helper(
                process.construct_signed_attestation_signature,
                process.dv_pubkey,
                process.peers
             )
    ensures inv_outputs_attestations_submited_are_valid(
                f_listen_for_attestation_shares(process, attestation_share).outputs,
                process'.dv_pubkey
                )
    { 
        var activate_att_consensus_intances := process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

        if  || (activate_att_consensus_intances == {} && !process.latest_attestation_duty.isPresent())
            || (activate_att_consensus_intances != {} && minInSet(activate_att_consensus_intances) <= attestation_share.data.slot)
            || (activate_att_consensus_intances == {} && !process.current_attestation_duty.isPresent() && process.latest_attestation_duty.isPresent() && process.latest_attestation_duty.safe_get().slot < attestation_share.data.slot) 
        {
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

            var process_with_new_att_shares_db := 
                    process.(
                        rcvd_attestation_shares := new_attestation_shares_db
                    );

                        
            if process_with_new_att_shares_db.construct_signed_attestation_signature(process_with_new_att_shares_db.rcvd_attestation_shares[attestation_share.data.slot][k]).isPresent() 
            {
                var aggregated_attestation := 
                    f_construct_aggregated_attestation_for_new_attestation_share(
                        attestation_share,
                        k, 
                        process_with_new_att_shares_db.construct_signed_attestation_signature,
                        process_with_new_att_shares_db.rcvd_attestation_shares
                    );

                var new_outputs := getEmptyOuputs().(
                                            attestations_submitted := {aggregated_attestation} 
                                        );

                var process_after_submitting_attestations := 
                    process_with_new_att_shares_db.(
                        bn := process_with_new_att_shares_db.bn.(
                            attestations_submitted := process_with_new_att_shares_db.bn.attestations_submitted + [aggregated_attestation]
                        )
                    );

                assert  process.construct_signed_attestation_signature
                        ==
                        process_after_submitting_attestations.construct_signed_attestation_signature
                        ;

                assert  && process.dv_pubkey == process_after_submitting_attestations.dv_pubkey
                        && process.peers == process_after_submitting_attestations.peers;

                var rcvd_attestation_shares := process_with_new_att_shares_db.rcvd_attestation_shares;
                var construct_signed_attestation_signature := process_with_new_att_shares_db.construct_signed_attestation_signature;
                
                assert  &&  attestation_share.data.slot in rcvd_attestation_shares.Keys
                        &&  k in rcvd_attestation_shares[attestation_share.data.slot]
                        &&  construct_signed_attestation_signature(rcvd_attestation_shares[attestation_share.data.slot][k]).isPresent()    
                        &&  all_att_shares_have_the_same_data(
                                rcvd_attestation_shares[attestation_share.data.slot][k], 
                                aggregated_attestation.data
                            )
                        &&  var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(aggregated_attestation.data.target.epoch));
                        &&  var attestation_signing_root := compute_attestation_signing_root(aggregated_attestation.data, fork_version);      
                        &&  signer_threshold(
                                process_with_new_att_shares_db.peers, 
                                rcvd_attestation_shares[attestation_share.data.slot][k], attestation_signing_root
                            ) 
                        &&  aggregated_attestation 
                            == 
                            f_construct_aggregated_attestation_for_new_attestation_share(
                                attestation_share,
                                k, 
                                construct_signed_attestation_signature,
                                rcvd_attestation_shares
                            )
                        ;
            }
            else 
            {
                assert inv_outputs_attestations_submited_are_valid(
                            f_listen_for_attestation_shares(process, attestation_share).outputs,
                            process'.dv_pubkey
                            );
            }
        }            
        else 
        {
            assert inv_outputs_attestations_submited_are_valid(
                        f_listen_for_attestation_shares(process, attestation_share).outputs,
                        process'.dv_pubkey
                        );
        }
            
    }

    lemma lem_inv_outputs_attestations_submited_are_valid_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    ensures inv_outputs_attestations_submited_are_valid(
                f_listen_for_new_imported_blocks(process, block).outputs,
                process'.dv_pubkey
                )
    { }  

    lemma lem_inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db_f_start_next_duty(
        process: Att_DVCState, 
        attestation_duty: AttestationDuty, 
        process': Att_DVCState)
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state    
    requires attestation_duty in process.all_rcvd_duties
    ensures && var outputs := f_start_next_duty(process, attestation_duty).outputs;
            && inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db(outputs, process')
    { }  

    lemma lem_inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db_f_resend_attestation_share(
        process: Att_DVCState,
        process': Att_DVCState
    )
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state    
    requires inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body(process)
    ensures && var outputs := f_resend_attestation_share(process).outputs;
            && inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db(outputs, process')
    {
        var new_outputs := getEmptyOuputs().(
                                    att_shares_sent :=
                                        multicast_multiple(process.attestation_shares_to_broadcast.Values, process.peers)
                                );

    }  

    lemma lem_inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state
    requires attestation_duty in process.all_rcvd_duties
    ensures && var outputs := f_check_for_next_duty(process, attestation_duty).outputs;
            && inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db(outputs, process')
    { }

    lemma lem_inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    ensures && var outputs := f_serve_attestation_duty(process, attestation_duty).outputs;
            && inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db(outputs, process')
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        
        lem_inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );   
    } 

    lemma lem_f_calc_att_with_sign_share_from_decided_att_data_verify_bls_signature(
        process: Att_DVCState,
        slot: Slot,
        att_data: AttestationData,
        att_share: AttestationShare
    )
    requires f_calc_att_with_sign_share_from_decided_att_data.requires(process, slot, att_data)
    requires att_share == f_calc_att_with_sign_share_from_decided_att_data(process, slot, att_data)
    ensures && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_data.target.epoch));
            && var attestation_signing_root := compute_attestation_signing_root(att_data, fork_version);
            && verify_bls_signature(
                    attestation_signing_root, 
                    att_share.signature, 
                    process.rs.pubkey
                )
    {
        

        var local_current_attestation_duty := process.current_attestation_duty.safe_get();
        var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_data.target.epoch));
        var attestation_signing_root := compute_attestation_signing_root(att_data, fork_version);
        var attestation_signature_share := rs_sign_attestation(att_data, fork_version, attestation_signing_root, process.rs);
        var attestation_with_signature_share := AttestationShare(
                    aggregation_bits := get_aggregation_bits(local_current_attestation_duty.validator_index),
                    data := att_data, 
                    signature := attestation_signature_share
                ); 
        
        rs_attestation_sign_and_verification_propeties();        
        assert verify_bls_signature(
                        attestation_signing_root,
                        rs_sign_attestation(att_data, fork_version, attestation_signing_root, process.rs),
                        process.rs.pubkey
                    );

    }
    

    lemma lem_inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state 
    ensures && var outputs := f_att_consensus_decided(process, id, decided_attestation_data).outputs;
            && inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db(outputs, process')
    { 
        if  is_decided_data_for_current_slot(process, decided_attestation_data, id)
        {
            var slashing_db_attestation := SlashingDBAttestation(
                                            source_epoch := decided_attestation_data.source.epoch,
                                            target_epoch := decided_attestation_data.target.epoch,
                                            signing_root := Some(hash_tree_root(decided_attestation_data)));
            var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);
            assert  slashing_db_attestation in new_attestation_slashing_db;

            var attestation_with_signature_share := f_calc_att_with_sign_share_from_decided_att_data(
                                                        process,
                                                        id,
                                                        decided_attestation_data
                                                    );     
            assert attestation_with_signature_share.data == decided_attestation_data;  

            var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
            var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
            lem_f_calc_att_with_sign_share_from_decided_att_data_verify_bls_signature(
                process,
                id,
                decided_attestation_data,
                attestation_with_signature_share
            );
            assert verify_bls_signature(
                        attestation_signing_root, 
                        attestation_with_signature_share.signature, 
                        process.rs.pubkey);
            assert verify_bls_signature(
                        attestation_signing_root, 
                        attestation_with_signature_share.signature, 
                        process'.rs.pubkey);

            assert  process'
                    ==
                    f_update_att_slashing_db_and_consensus_engine_after_att_consensus_decided(
                            process,
                            id,
                            decided_attestation_data,
                            attestation_with_signature_share,
                            new_attestation_slashing_db
                        );           

            assert  f_att_consensus_decided(process, id, decided_attestation_data).outputs
                    ==
                    getEmptyOuputs().(
                        att_shares_sent := multicast(attestation_with_signature_share, process.peers)
                    );

            var outputs := f_att_consensus_decided(process, id, decided_attestation_data).outputs;

            forall att_share: AttestationShare | att_share in getMessagesFromMessagesWithRecipient(outputs.att_shares_sent) 
            {
                assert inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db_body(process', att_share);
            }
        }     
        else 
        {
            var outputs := f_att_consensus_decided(process, id, decided_attestation_data).outputs;
            assert inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db(outputs, process');
        }

    }  
    
    lemma lem_inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    ensures && var outputs := f_listen_for_attestation_shares(process, attestation_share).outputs;
            && inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db(outputs, process')
    { }

    lemma lem_inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    ensures && var outputs := f_listen_for_new_imported_blocks(process, block).outputs;
            && inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db(outputs, process')
    { }  

    lemma lem_inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state
    requires attestation_duty in process.all_rcvd_duties
    requires inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body(process)
    ensures inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body(process')
    { }

    lemma lem_inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body(process)
    ensures inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body(process')
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        
        lem_inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );   
    }  

    lemma lem_inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state 
    requires inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body(process)
    ensures inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body(process')
    { 
        if  is_decided_data_for_current_slot(process, decided_attestation_data, id)
        {
            var slashing_db_attestation := SlashingDBAttestation(
                                            source_epoch := decided_attestation_data.source.epoch,
                                            target_epoch := decided_attestation_data.target.epoch,
                                            signing_root := Some(hash_tree_root(decided_attestation_data)));
            var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);
            assert  slashing_db_attestation in new_attestation_slashing_db;

            var attestation_with_signature_share := f_calc_att_with_sign_share_from_decided_att_data(
                                                        process,
                                                        id,
                                                        decided_attestation_data
                                                    );     
            assert attestation_with_signature_share.data == decided_attestation_data;  

            var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
            var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
            lem_f_calc_att_with_sign_share_from_decided_att_data_verify_bls_signature(
                process,
                id,
                decided_attestation_data,
                attestation_with_signature_share
            );
            assert verify_bls_signature(
                        attestation_signing_root, 
                        attestation_with_signature_share.signature, 
                        process.rs.pubkey);
            assert verify_bls_signature(
                        attestation_signing_root, 
                        attestation_with_signature_share.signature, 
                        process'.rs.pubkey);

            assert  process'
                    ==
                    f_update_att_slashing_db_and_consensus_engine_after_att_consensus_decided(
                            process,
                            id,
                            decided_attestation_data,
                            attestation_with_signature_share,
                            new_attestation_slashing_db
                        );           

            assert  f_att_consensus_decided(process, id, decided_attestation_data).outputs
                    ==
                    getEmptyOuputs().(
                        att_shares_sent := multicast(attestation_with_signature_share, process.peers)
                    );            
        }     
        else 
        {
            var outputs := f_att_consensus_decided(process, id, decided_attestation_data).outputs;
            assert inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body(process');
        }

    } 

    lemma lem_inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body(process)
    ensures inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body(process')
    { }

    lemma lem_inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body(process)
    ensures inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body(process')
    { }  

    lemma lem_inv_outputs_attestations_submited_are_created_based_on_shares_of_a_quorum_f_start_next_duty(
        process: Att_DVCState, 
        attestation_duty: AttestationDuty, 
        process': Att_DVCState
    )
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state    
    ensures inv_outputs_attestations_submited_are_created_based_on_shares_of_a_quorum(                
                f_start_next_duty(process, attestation_duty).outputs,
                process'
            )
    { }  

    lemma lem_inv_outputs_attestations_submited_are_created_based_on_shares_of_a_quorum_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state
    ensures inv_outputs_attestations_submited_are_created_based_on_shares_of_a_quorum(
                f_check_for_next_duty(process, attestation_duty).outputs,
                process'
            )
    { }

    lemma lem_inv_outputs_attestations_submited_are_created_based_on_shares_of_a_quorum_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    ensures inv_outputs_attestations_submited_are_created_based_on_shares_of_a_quorum(
                f_serve_attestation_duty(process, attestation_duty).outputs,
                process'
            )
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        lem_inv_outputs_attestations_submited_are_created_based_on_shares_of_a_quorum_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );   
    } 

    lemma lem_inv_outputs_attestations_submited_are_created_based_on_shares_of_a_quorum_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    ensures inv_outputs_attestations_submited_are_created_based_on_shares_of_a_quorum(
                f_listen_for_new_imported_blocks(process, block).outputs,
                process'
            )
    { }  

    lemma lem_inv_outputs_attestations_submited_are_created_based_on_shares_of_a_quorum_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        process': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires construct_signed_attestation_signature_assumptions_helper(
                process.construct_signed_attestation_signature,
                process.dv_pubkey,
                process.peers
             )
    ensures inv_outputs_attestations_submited_are_created_based_on_shares_of_a_quorum(
                f_listen_for_attestation_shares(process, attestation_share).outputs,
                process'
                )
    { 
        var activate_att_consensus_intances := process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

        if  || (activate_att_consensus_intances == {} && !process.latest_attestation_duty.isPresent())
            || (activate_att_consensus_intances != {} && minInSet(activate_att_consensus_intances) <= attestation_share.data.slot)
            || (activate_att_consensus_intances == {} && !process.current_attestation_duty.isPresent() && process.latest_attestation_duty.isPresent() && process.latest_attestation_duty.safe_get().slot < attestation_share.data.slot) 
        {
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

            var process_with_new_att_shares_db := 
                    process.(
                        rcvd_attestation_shares := new_attestation_shares_db
                    );

                        
            if process_with_new_att_shares_db.construct_signed_attestation_signature(process_with_new_att_shares_db.rcvd_attestation_shares[attestation_share.data.slot][k]).isPresent() 
            {
                var aggregated_attestation := 
                    f_construct_aggregated_attestation_for_new_attestation_share(
                        attestation_share,
                        k, 
                        process_with_new_att_shares_db.construct_signed_attestation_signature,
                        process_with_new_att_shares_db.rcvd_attestation_shares
                    );

                var new_outputs := getEmptyOuputs().(
                                            attestations_submitted := {aggregated_attestation} 
                                        );

                var process_after_submitting_attestations := 
                    process_with_new_att_shares_db.(
                        bn := process_with_new_att_shares_db.bn.(
                            attestations_submitted := process_with_new_att_shares_db.bn.attestations_submitted + [aggregated_attestation]
                        )
                    );

                assert  process.construct_signed_attestation_signature
                        ==
                        process_after_submitting_attestations.construct_signed_attestation_signature
                        ;

                assert  && process.dv_pubkey == process_after_submitting_attestations.dv_pubkey
                        && process.peers == process_after_submitting_attestations.peers;

                var rcvd_attestation_shares := process_with_new_att_shares_db.rcvd_attestation_shares;
                var construct_signed_attestation_signature := process_with_new_att_shares_db.construct_signed_attestation_signature;
                
                assert  &&  attestation_share.data.slot in rcvd_attestation_shares.Keys
                        &&  k in rcvd_attestation_shares[attestation_share.data.slot]
                        &&  construct_signed_attestation_signature(rcvd_attestation_shares[attestation_share.data.slot][k]).isPresent()    
                        &&  all_att_shares_have_the_same_data(
                                rcvd_attestation_shares[attestation_share.data.slot][k], 
                                aggregated_attestation.data
                            )
                        &&  var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(aggregated_attestation.data.target.epoch));
                        &&  var attestation_signing_root := compute_attestation_signing_root(aggregated_attestation.data, fork_version);      
                        &&  signer_threshold(
                                process_with_new_att_shares_db.peers, 
                                rcvd_attestation_shares[attestation_share.data.slot][k], attestation_signing_root
                            ) 
                        &&  aggregated_attestation 
                            == 
                            f_construct_aggregated_attestation_for_new_attestation_share(
                                attestation_share,
                                k, 
                                construct_signed_attestation_signature,
                                rcvd_attestation_shares
                            )
                        ;
            }
            else 
            {
                assert inv_outputs_attestations_submited_are_created_based_on_shares_of_a_quorum(
                            f_listen_for_attestation_shares(process, attestation_share).outputs,
                            process'
                            );
            }
        }            
        else 
        {
            assert inv_outputs_attestations_submited_are_created_based_on_shares_of_a_quorum(
                        f_listen_for_attestation_shares(process, attestation_share).outputs,
                        process'
                        );
        }
            
    }

    lemma lem_inv_outputs_attestations_submited_are_created_based_on_shares_of_a_quorum_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state 
    ensures inv_outputs_attestations_submited_are_created_based_on_shares_of_a_quorum(
                f_att_consensus_decided(process, id, decided_attestation_data).outputs,
                process'
                )
    { }  

    lemma lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_f_terminate_current_attestation_duty(
        allMessagesSent: set<AttestationShare>,
        process: Att_DVCState, 
        process': Att_DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
    { }    

    lemma lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_f_start_next_duty(
        allMessagesSent: set<AttestationShare>,
        process: Att_DVCState, 
        attestation_duty: AttestationDuty, 
        process': Att_DVCState
    )
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires (  forall att_share: AttestationShare |
                    && att_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_the_owner_of_att_share(rs_pubkey, att_share)
                    ::
                    && inv_sent_att_shares_have_corresponding_slashing_db_attestations_body(process, att_share)             
            )
    requires inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
    { 
        var rs_pubkey: BLSPubkey := process.rs.pubkey;
        assert rs_pubkey == process'.rs.pubkey;

        var duty_slot := attestation_duty.slot;
        var attestation_slashing_db := process.attestation_slashing_db;
        var attestation_slashing_db' := process'.attestation_slashing_db;
        assert attestation_slashing_db == attestation_slashing_db';
        assert  (  forall att_share: AttestationShare |
                    && att_share in allMessagesSent 
                    && pred_is_the_owner_of_att_share(rs_pubkey, att_share)
                    ::
                    && inv_sent_att_shares_have_corresponding_slashing_db_attestations_body(process', att_share)             
                );

        var att_slashing_db_hist: map<Slot, map<AttestationData -> bool, set<set<SlashingDBAttestation>>>> 
            := process.attestation_consensus_engine_state.att_slashing_db_hist;        
        var att_slashing_db_hist': map<Slot, map<AttestationData -> bool, set<set<SlashingDBAttestation>>>> 
            := process'.attestation_consensus_engine_state.att_slashing_db_hist;

        var acvc := 
            AttestationConsensusValidityCheckState(
                attestation_duty := attestation_duty,
                validityPredicate := (ad: AttestationData) => ci_decision_is_valid_attestation_data(attestation_slashing_db, ad, attestation_duty)
            );
        var new_vp := acvc.validityPredicate;
        var new_active_attestation_consensus_instances := 
            process.attestation_consensus_engine_state.active_attestation_consensus_instances[
                duty_slot := acvc
            ];              

        assert process.rs.pubkey == process'.rs.pubkey;

        forall slot: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation> | 
            && slot in att_slashing_db_hist'
            && vp in att_slashing_db_hist'[slot].Keys
            && db in att_slashing_db_hist'[slot][vp]
        ensures inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_body(            
                        allMessagesSent,
                        process'.rs.pubkey,
                        slot,
                        vp,
                        db
                    );   
        {
            if slot != duty_slot || vp != new_vp
            {
                assert inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_body(            
                    allMessagesSent,
                    process.rs.pubkey,
                    slot,
                    vp,
                    db
                );                
            }
            else
            {
                var hist_slot := getOrDefault(att_slashing_db_hist, slot, map[]);
                var hist_slot_vp := getOrDefault(hist_slot, vp, {});
                var new_hist_slot := getOrDefault(att_slashing_db_hist', slot, map[]);
                var new_hist_slot_vp := getOrDefault(new_hist_slot, vp, {});
                
                assert hist_slot_vp + {attestation_slashing_db} == new_hist_slot_vp;

                if db in hist_slot_vp
                {                    
                    assert  inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_body(            
                                allMessagesSent,
                                process'.rs.pubkey,
                                slot,
                                vp,
                                db
                            );   
                }
                else
                {
                    assert db == attestation_slashing_db;
                    forall att_share: AttestationShare |
                                && att_share in allMessagesSent 
                                && pred_is_the_owner_of_att_share(rs_pubkey, att_share)
                    {
                        var att_data := att_share.data;
                        var slashing_db_attestation 
                            := 
                            SlashingDBAttestation(
                                source_epoch := att_data.source.epoch,
                                target_epoch := att_data.target.epoch,
                                signing_root := Some(hash_tree_root(att_data))
                            );
                        assert inv_sent_att_shares_have_corresponding_slashing_db_attestations_body(process', att_share);
                        assert slashing_db_attestation in process'.attestation_slashing_db;     
                        assert slashing_db_attestation in db;                    
                    }
                }
            }
        }
    }  

    lemma lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_updateAttSlashingDBHist(
        hist: map<Slot, map<AttestationData -> bool, set<set<SlashingDBAttestation>>>>,
        new_active_attestation_consensus_instances : map<Slot, AttestationConsensusValidityCheckState>,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        new_hist: map<Slot, map<AttestationData -> bool, set<set<SlashingDBAttestation>>>>,
        allMessagesSent: set<AttestationShare>,
        rs_pubkey: BLSPubkey
    )    
    requires new_hist == updateAttSlashingDBHist(hist, new_active_attestation_consensus_instances, new_attestation_slashing_db)
    requires (  forall slot: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation> | 
                        && slot in hist
                        && vp in hist[slot].Keys
                        && db in hist[slot][vp]
                        :: 
                        inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_body(
                            allMessagesSent,
                            rs_pubkey,
                            slot,
                            vp,
                            db
                        )
    )
    requires (  forall att_share: AttestationShare | 
                        && att_share in allMessagesSent 
                        && pred_is_the_owner_of_att_share(rs_pubkey, att_share)
                        ::
                        && var att_data := att_share.data;
                        && var slashing_db_attestation := construct_SlashingDBAttestation_from_att_data(att_data);
                        && slashing_db_attestation in new_attestation_slashing_db           
    )
    ensures ( forall slot: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation>, att_share: AttestationShare | 
                    && slot in new_hist.Keys
                    && vp in new_hist[slot].Keys
                    && db in new_hist[slot][vp]
                    && att_share in allMessagesSent
                    && pred_is_the_owner_of_att_share(rs_pubkey, att_share)
                    && att_share.data.slot < slot             
                    ::
                    inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_body(
                        allMessagesSent,
                        rs_pubkey,
                        slot,
                        vp,
                        db
                    )
    )
    {
        assert hist.Keys + new_active_attestation_consensus_instances.Keys == new_hist.Keys;

        forall slot: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation>, att_share: AttestationShare | 
                    && slot in new_hist.Keys
                    && vp in new_hist[slot].Keys
                    && db in new_hist[slot][vp]
                    && att_share in allMessagesSent
                    && pred_is_the_owner_of_att_share(rs_pubkey, att_share)
                    && att_share.data.slot < slot             
        ensures inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_body(
                        allMessagesSent,
                        rs_pubkey,
                        slot,
                        vp,
                        db
                    )
        {
            if slot in new_active_attestation_consensus_instances.Keys
            {
                if slot in hist.Keys && vp in hist[slot].Keys && db in hist[slot][vp]
                {                    
                    assert inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_body(
                        allMessagesSent,
                        rs_pubkey,
                        slot,
                        vp,
                        db
                    );                
                }
                else
                {
                    assert db == new_attestation_slashing_db;
                    assert inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_body(
                        allMessagesSent,
                        rs_pubkey,
                        slot,
                        vp,
                        db
                    );      
                }
            }
            else
            {
                assert hist[slot] == new_hist[slot];
                assert inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_body(
                            allMessagesSent,
                            rs_pubkey,
                            slot,
                            vp,
                            db
                        );
            }
        }
    }

    lemma lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_updateConsensusInstanceValidityCheck(
        s: ConsensusEngineState,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState,
        allMessagesSent: set<AttestationShare>
    )
    requires s' == updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db)
    {
        var new_active_attestation_consensus_instances := updateConsensusInstanceValidityCheckHelper(
                    s.active_attestation_consensus_instances,
                    new_attestation_slashing_db
                );

        forall slot: Slot | slot in new_active_attestation_consensus_instances.Keys
        ensures && var validityPredicate := new_active_attestation_consensus_instances[slot].validityPredicate;
                && var attestation_duty := new_active_attestation_consensus_instances[slot].attestation_duty;
                && ( forall att_data: AttestationData 
                        ::
                        validityPredicate(att_data)
                        <==> 
                        ci_decision_is_valid_attestation_data(new_attestation_slashing_db, att_data, attestation_duty)
                )
        {
            var validityPredicate := new_active_attestation_consensus_instances[slot].validityPredicate;
            var attestation_duty := new_active_attestation_consensus_instances[slot].attestation_duty;
            assert  ( forall att_data: AttestationData 
                        ::
                        validityPredicate(att_data)
                        <==> 
                        ci_decision_is_valid_attestation_data(new_attestation_slashing_db, att_data, attestation_duty)
                    )
            ;
        }

        assert  s' 
                ==
                s.(
                    active_attestation_consensus_instances := new_active_attestation_consensus_instances,
                    att_slashing_db_hist := updateAttSlashingDBHist(
                        s.att_slashing_db_hist,
                        new_active_attestation_consensus_instances,
                        new_attestation_slashing_db
                    )
                );
    }

    lemma lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_f_check_for_next_duty(
        allMessagesSent: set<AttestationShare>,
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state
    requires (  forall att_share: AttestationShare |
                    && att_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_the_owner_of_att_share(rs_pubkey, att_share)
                    ::
                    && inv_sent_att_shares_have_corresponding_slashing_db_attestations_body(process, att_share)             
            )
    requires inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
    { 
        if attestation_duty.slot in process.future_att_consensus_instances_already_decided.Keys 
        {
            
            var new_attestation_slashing_db := 
                f_update_attestation_slashing_db(
                    process.attestation_slashing_db, 
                    process.future_att_consensus_instances_already_decided[attestation_duty.slot]
                );
            assert process.attestation_slashing_db <= new_attestation_slashing_db;

            var new_active_attestation_consensus_instances := updateConsensusInstanceValidityCheckHelper(
                    process.attestation_consensus_engine_state.active_attestation_consensus_instances,
                    new_attestation_slashing_db
                );

            var new_process := 
                process.(
                    current_attestation_duty := Some(attestation_duty),
                    latest_attestation_duty := Some(attestation_duty),
                    future_att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided - {attestation_duty.slot},
                    attestation_slashing_db := new_attestation_slashing_db,
                    attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                        process.attestation_consensus_engine_state,
                        new_attestation_slashing_db
                    )                        
                );

            lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_updateAttSlashingDBHist(
                process.attestation_consensus_engine_state.att_slashing_db_hist,                 
                new_active_attestation_consensus_instances,
                new_attestation_slashing_db,
                process'.attestation_consensus_engine_state.att_slashing_db_hist,
                allMessagesSent,
                process.rs.pubkey
            );
        
        }
        else
        {
            lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_f_start_next_duty(
                allMessagesSent,
                process, 
                attestation_duty, 
                process'
            );
        }
    }  

    lemma lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_f_serve_attestation_duty(
        allMessagesSent: set<AttestationShare>,
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires (  forall att_share: AttestationShare |
                    && att_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_the_owner_of_att_share(rs_pubkey, att_share)
                    ::
                    && inv_sent_att_shares_have_corresponding_slashing_db_attestations_body(process, att_share)             
            )
    requires inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        assert  inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(                
                    allMessagesSent,
                    process_rcvd_duty
                );
        assert  (  forall att_share: AttestationShare |
                                && att_share in allMessagesSent 
                                && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                                && pred_is_the_owner_of_att_share(rs_pubkey, att_share)
                                ::
                                && inv_sent_att_shares_have_corresponding_slashing_db_attestations_body(process_rcvd_duty, att_share)             
                );

        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);

        lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_f_terminate_current_attestation_duty(
            allMessagesSent,
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        assert  (  forall att_share: AttestationShare |
                                && att_share in allMessagesSent 
                                && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                                && pred_is_the_owner_of_att_share(rs_pubkey, att_share)
                                ::
                                && inv_sent_att_shares_have_corresponding_slashing_db_attestations_body(process_after_stopping_active_consensus_instance, att_share)             
                );

        lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_f_check_for_next_duty(
            allMessagesSent,
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );   
    } 

     
    lemma lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_f_listen_for_new_imported_blocks(
        allMessagesSent: set<AttestationShare>,
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires (  forall att_share: AttestationShare |
                    && att_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_the_owner_of_att_share(rs_pubkey, att_share)
                    ::
                    && inv_sent_att_shares_have_corresponding_slashing_db_attestations_body(process, att_share)             
            )
    requires inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
    { 
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
                f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var process_after_stopping_consensus_instance :=
                process.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );         

        assert inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process_after_stopping_consensus_instance
            );          
        assert (  forall att_share: AttestationShare |
                    && att_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_the_owner_of_att_share(rs_pubkey, att_share)
                    ::
                    && inv_sent_att_shares_have_corresponding_slashing_db_attestations_body(process_after_stopping_consensus_instance, att_share)             
            );

        if process_after_stopping_consensus_instance.current_attestation_duty.isPresent() && process_after_stopping_consensus_instance.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided 
        {
            var decided_attestation_data := att_consensus_instances_already_decided[process_after_stopping_consensus_instance.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(process_after_stopping_consensus_instance.attestation_slashing_db, decided_attestation_data);
            var process_after_updating_validity_check := process_after_stopping_consensus_instance.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    process_after_stopping_consensus_instance.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )
            );

            assert process_after_updating_validity_check == process';
            assert process_after_stopping_consensus_instance.attestation_slashing_db <= new_attestation_slashing_db;

            var new_active_attestation_consensus_instances := updateConsensusInstanceValidityCheckHelper(
                    process_after_stopping_consensus_instance.attestation_consensus_engine_state.active_attestation_consensus_instances,
                    new_attestation_slashing_db
                );

            assert  process'.attestation_consensus_engine_state.att_slashing_db_hist 
                    == 
                    updateAttSlashingDBHist(
                        process_after_stopping_consensus_instance.attestation_consensus_engine_state.att_slashing_db_hist, 
                        new_active_attestation_consensus_instances, 
                        new_attestation_slashing_db
                    );

            lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_updateAttSlashingDBHist(
                process_after_stopping_consensus_instance.attestation_consensus_engine_state.att_slashing_db_hist,                 
                new_active_attestation_consensus_instances,
                new_attestation_slashing_db,
                process'.attestation_consensus_engine_state.att_slashing_db_hist,
                allMessagesSent,
                process.rs.pubkey
            );
        }
        else
        {
            assert inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            );
        }
    }  

    lemma lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_f_att_consensus_decided_new_att_shares_sent(
        allMessagesSent: set<AttestationShare>,
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires (  forall att_share: AttestationShare |
                    && att_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_the_owner_of_att_share(rs_pubkey, att_share)
                    ::
                    && inv_sent_att_shares_have_corresponding_slashing_db_attestations_body(process, att_share)             
            )
    requires inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    requires && process.current_attestation_duty.isPresent()
             && id == process.current_attestation_duty.safe_get().slot
             && id == decided_attestation_data.slot
    requires inv_available_current_att_duty_is_latest_att_duty_body(process)
    requires ( forall slot | slot in process'.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                        ::
                        slot <= process'.latest_attestation_duty.safe_get().slot
             )
    ensures && var outputs := f_att_consensus_decided(process, id, decided_attestation_data).outputs;
            && var allMessagesSent' := allMessagesSent + getMessagesFromMessagesWithRecipient(outputs.att_shares_sent);
            && inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(                
                    allMessagesSent',
                    process'
                )
    ensures && var attestation_with_signature_share := f_calc_att_with_sign_share_from_decided_att_data(
                                                    process,
                                                    id,
                                                    decided_attestation_data
                                                );       
            && pred_is_the_owner_of_att_share(process'.rs.pubkey, attestation_with_signature_share)
            && ( forall slot: Slot | slot in process'.attestation_consensus_engine_state.att_slashing_db_hist.Keys ::
                    attestation_with_signature_share.data.slot >= slot
            )
    {
        var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);

        var attestation_with_signature_share := f_calc_att_with_sign_share_from_decided_att_data(
                                                    process,
                                                    id,
                                                    decided_attestation_data
                                                );       
        lem_f_calc_att_with_sign_share_from_decided_att_data_verify_bls_signature(
            process,
            id,
            decided_attestation_data,
            attestation_with_signature_share
        );
        assert pred_is_the_owner_of_att_share(process.rs.pubkey, attestation_with_signature_share);
        assert process'.rs.pubkey == process.rs.pubkey;
        assert pred_is_the_owner_of_att_share(process'.rs.pubkey, attestation_with_signature_share);

        assert process.attestation_slashing_db <= new_attestation_slashing_db;                                                    

        assert  process'
                ==
                f_update_att_slashing_db_and_consensus_engine_after_att_consensus_decided(
                        process,
                        id,
                        decided_attestation_data,
                        attestation_with_signature_share,
                        new_attestation_slashing_db
                    );   

        
        assert process.latest_attestation_duty.isPresent();
        assert && process'.latest_attestation_duty.isPresent()
               && process'.latest_attestation_duty.safe_get()
                  ==
                  process.latest_attestation_duty.safe_get()  ;

        var new_active_attestation_consensus_instances := updateConsensusInstanceValidityCheckHelper(
                process.attestation_consensus_engine_state.active_attestation_consensus_instances,
                new_attestation_slashing_db
            );        

        lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_updateAttSlashingDBHist(
            process.attestation_consensus_engine_state.att_slashing_db_hist,                 
            new_active_attestation_consensus_instances,
            new_attestation_slashing_db,
            process'.attestation_consensus_engine_state.att_slashing_db_hist,
            allMessagesSent,
            process.rs.pubkey
        );

        assert  inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(
                    allMessagesSent,
                    process'
                );
        assert process.rs.pubkey == process'.rs.pubkey;

        var allMessagesSent' := allMessagesSent + {attestation_with_signature_share};

        forall slot: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation> | 
                    && slot in process'.attestation_consensus_engine_state.att_slashing_db_hist
                    && vp in process'.attestation_consensus_engine_state.att_slashing_db_hist[slot]
                    && db in process'.attestation_consensus_engine_state.att_slashing_db_hist[slot][vp]
        ensures inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_body(
                    allMessagesSent',
                    process'.rs.pubkey,
                    slot,
                    vp,
                    db
                )
        {
            var hist := process.attestation_consensus_engine_state.att_slashing_db_hist;
            var hist' := process'.attestation_consensus_engine_state.att_slashing_db_hist;            
            var hist_slot := getOrDefault(hist, slot, map[]);
            var hist_slot' := getOrDefault(hist', slot, map[]);
            var hist_slot_vp := getOrDefault(hist_slot, vp, {});
            var hist_slot_vp' := getOrDefault(hist_slot', vp, {});

            assert || hist_slot_vp' == hist_slot_vp 
                   || hist_slot_vp' == hist_slot_vp + {new_attestation_slashing_db};

            forall att_share: AttestationShare | 
                && att_share in allMessagesSent'
                && pred_is_the_owner_of_att_share(process'.rs.pubkey, att_share)
                && att_share.data.slot < slot
            ensures && var att_data := att_share.data;
                    && var slashing_db_attestation := SlashingDBAttestation(
                                                    source_epoch := att_data.source.epoch,
                                                    target_epoch := att_data.target.epoch,
                                                    signing_root := Some(hash_tree_root(att_data)));
                    && slashing_db_attestation in db
            {
                var att_data := att_share.data;
                var slashing_db_attestation := SlashingDBAttestation(
                                                    source_epoch := att_data.source.epoch,
                                                    target_epoch := att_data.target.epoch,
                                                    signing_root := Some(hash_tree_root(att_data)));
                
                if att_share in allMessagesSent
                {
                    assert slashing_db_attestation in db;
                }
                else
                {
                    
                    assert att_share == attestation_with_signature_share;
                    assert att_share.data.slot >= slot;
                }
                assert slashing_db_attestation in db;
            }
        }
    }

    lemma lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_f_att_consensus_decided(
        allMessagesSent: set<AttestationShare>,
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state         
    requires (  forall att_share: AttestationShare |
                    && att_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_the_owner_of_att_share(rs_pubkey, att_share)
                    ::
                    && inv_sent_att_shares_have_corresponding_slashing_db_attestations_body(process, att_share)             
            )
    requires inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
             )          
    { 
        if  && process.current_attestation_duty.isPresent()
            && id == process.current_attestation_duty.safe_get().slot
            && id == decided_attestation_data.slot
        {
            
        }
        else 
        {
            assert inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            );
        }
            
    }

    lemma lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_f_resend_attestation_share(
        allMessagesSent: set<AttestationShare>,
        process: Att_DVCState,
        process': Att_DVCState
    )
    requires f_resend_attestation_share.requires(process)
    requires process' == f_resend_attestation_share(process).state       
    requires process.attestation_shares_to_broadcast.Values <= allMessagesSent 
    requires inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
    { }

    lemma lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body_f_terminate_current_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState,
        n: BLSPubkey
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body(process')
    { }  

    lemma lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body_f_start_next_duty_helper(
        s: ConsensusEngineState,
        id: Slot,
        attestation_duty: AttestationDuty,
        attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState
    )
    requires startConsensusInstance.requires(s, id, attestation_duty, attestation_slashing_db)
    requires s' == startConsensusInstance(s, id, attestation_duty, attestation_slashing_db)
    ensures s.active_attestation_consensus_instances.Keys + { id } == s'.active_attestation_consensus_instances.Keys
    { }  

    lemma lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body_f_start_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_start_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body(process')
    {
        lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body_f_start_next_duty_helper(
            process.attestation_consensus_engine_state,
            attestation_duty.slot,
            attestation_duty,
            process.attestation_slashing_db,
            process'.attestation_consensus_engine_state
        );
    }  

    lemma lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state  
    requires inv_an_att_duty_in_the_next_delivery_is_not_lower_than_latest_att_duty_body(process, attestation_duty)
    requires inv_the_domain_of_active_attestation_consensus_instances_is_a_subset_of_att_slashing_db_hist_body(process)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body(process')
    { 
        if attestation_duty.slot in process.future_att_consensus_instances_already_decided.Keys 
        {
            var new_attestation_slashing_db := 
                f_update_attestation_slashing_db(
                    process.attestation_slashing_db, 
                    process.future_att_consensus_instances_already_decided[attestation_duty.slot]
                );
            var new_active_attestation_consensus_instances := 
                updateConsensusInstanceValidityCheckHelper(
                    process.attestation_consensus_engine_state.active_attestation_consensus_instances,
                    new_attestation_slashing_db
                );
            assert  new_active_attestation_consensus_instances.Keys 
                    <= 
                    process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
                    <= 
                    process.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                    ;
            assert  process'.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                    ==
                    process.attestation_consensus_engine_state.att_slashing_db_hist.Keys + new_active_attestation_consensus_instances.Keys
                    ==
                    process.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                    ;
            
        }
        else
        { 
            lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body_f_start_next_duty(process, attestation_duty, process');
        }
    } 

    lemma lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state  
    requires inv_an_att_duty_in_the_next_delivery_is_not_lower_than_latest_att_duty_body(process, attestation_duty)
    requires inv_the_domain_of_active_attestation_consensus_instances_is_a_subset_of_att_slashing_db_hist_body(process)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body(process')
    { 
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );
    }  

    lemma lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        process': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body(process)
    requires inv_the_domain_of_active_attestation_consensus_instances_is_a_subset_of_att_slashing_db_hist_body(process)   
    ensures inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body(process')
    { }        

    lemma lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        process': Att_DVCState    
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body(process)
    requires inv_the_domain_of_active_attestation_consensus_instances_is_a_subset_of_att_slashing_db_hist_body(process)   
    ensures inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body(process')
    { }            
}