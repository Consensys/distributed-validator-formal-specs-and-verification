include "../../../common/commons.dfy"
include "../common/attestation_creation_instrumented.dfy"
include "../../../specs/consensus/consensus.dfy"
include "../../../specs/network/network.dfy"
include "../../../specs/dv/dv_attestation_creation.dfy"
include "inv.dfy"
include "fnc_invs_1_26.dfy"
include "../../common/helper_sets_lemmas.dfy"
include "proofs_intermediate_steps.dfy"
include "dv_next_invs_1_7.dfy"
include "dv_next_invs_8_18.dfy"
include "dv_next_invs_19_26.dfy"
include "invs_dv_next_4.dfy"
include "ind_inv.dfy"
include "ind_inv2.dfy"
include "ind_inv3.dfy"
include "ind_inv4.dfy"
include "core_proofs.dfy"


module Proofs_DV_Ind_Inv
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Att_Ind_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Att_Ind_Inv_With_Empty_Initial_Attestation_Slashing_DB2
    import opened Fnc_Invs_1_26
    import opened Helper_Sets_Lemmas
    import opened DV_Next_Invs_1_7
    import opened DV_Next_Invs_8_18
    import opened DV_Next_Invs_19_26
    import opened Proofs_Intermediate_Steps
    import opened DV_Next_Invs_27_37
    import opened Core_Proofs
    import opened IndInv3
    import opened IndInv4

    predicate ind_inv(dv: DVState)       
    {
        && invs_1_7(dv)
        && invs_8_18(dv)
        && invs_19_26(dv)
        && invs_27_37(dv)
        && invs_other_properties_1(dv)
        && invs_other_properties_2(dv)
        && invs_other_properties_3(dv)
        && invs_other_properties_4(dv)
        && invs_other_properties_5(dv)
        && invs_other_properties_6(dv)
        && invs_other_properties_7(dv)
        && inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue(dv)
    }

    predicate invs_1_7(dv: DVState)       
    {
        &&  inv_quorum_constraints(dv)
        &&  inv_unchanged_honesty(dv)
        &&  inv_only_dv_construct_signed_attestation_signature(dv)
        &&  inv_queued_att_duty_is_dvn_seq_of_att_duty(dv)
        &&  inv_queued_att_duty_is_rcvd_duty(dv)
        &&  inv_current_att_duty_is_rcvd_duty(dv)
        &&  inv_latest_served_duty_is_rcvd_duty(dv)
    }

    predicate invs_8_18(dv: DVState)       
    {        
        &&  inv_none_latest_served_duty_implies_none_current_att_duty(dv)   
        &&  inv_current_att_duty_is_either_none_or_latest_served_duty(dv)  
        &&  inv_not_none_current_att_duty_is_latest_served_att_duty(dv) 
        &&  inv_is_sequence_attestation_duties_to_be_serves_orders(dv)      
        &&  inv_no_queued_att_duty_if_latest_served_att_duty_is_none(dv)  
        &&  inv_strictly_increasing_queue_of_att_duties(dv)  
        &&  inv_queued_att_duty_is_higher_than_latest_served_att_duty(dv)  
    }
    
    predicate invs_19_26(dv: DVState)       
    {        
        &&  inv_no_duplicated_att_duties(dv)           
        &&  inv_every_att_duty_before_dvn_att_index_was_delivered(dv) 
        &&  inv_no_active_consensus_instance_before_receiving_att_duty(dv)      
        &&  inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty(dv)  
        &&  inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty(dv)          
        &&  inv_consensus_instances_only_for_rcvd_duties(dv)  
    }

    predicate invs_27_37(dv: DVState)       
    {                
        &&  inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties(dv)  
        &&  inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred(dv)  
        &&  inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k(dv)  
        &&  inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db(dv)  
        &&  inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist(dv)
        &&  inv_construct_signed_attestation_signature_assumptions_helper(dv)
        &&  inv_all_in_transit_messages_were_sent(dv)
        &&  inv_rcvd_attn_shares_are_from_sent_messages(dv)
        &&  IndInv3.inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper(dv)
    }


    
    lemma lemma_ind_inv_dv_init(dv: DVState)       
    requires DV.Init(dv, {})    
    ensures ind_inv(dv)
    ensures NextPreCond(dv)
    {
        assert  DV.Init(dv, {})  
                ==>                 
                && invs_1_7(dv)
                && invs_8_18(dv)
                && invs_19_26(dv)
                && invs_27_37(dv);

        assert  DV.Init(dv, {})    
                ==>
                && invs_other_properties_1(dv)
                && invs_other_properties_2(dv)
                && invs_other_properties_3(dv)
                && invs_other_properties_4(dv)
                && invs_other_properties_5(dv)
                && invs_other_properties_6(dv)
                ;
    }  

    

    

    lemma lemma_ind_inv_dv_next_invs_1_7(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_1_7(dv')
    {    
        lemma_inv_quorum_constraints_dv_next(dv, e, dv');
        lemma_inv_unchanged_honesty_dv_next(dv, e, dv');
        lemma_inv_only_dv_construct_signed_attestation_signature_dv_next(dv, e, dv');
        lemma_inv_queued_att_duty_is_dvn_seq_of_att_duty_dv_next(dv, e, dv');
        lemma_inv_queued_att_duty_is_rcvd_duty_dv_next(dv, e, dv');
        lemma_inv_current_att_duty_is_rcvd_duty_dv_next(dv, e, dv');
        lemma_inv_latest_served_duty_is_rcvd_duty_dv_next(dv, e, dv');        
    }

    lemma lemma_ind_inv_dv_next_invs_8_18_helper_1(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_none_latest_served_duty_implies_none_current_att_duty(dv')
    ensures inv_current_att_duty_is_either_none_or_latest_served_duty(dv')
    ensures inv_not_none_current_att_duty_is_latest_served_att_duty(dv')
    ensures inv_is_sequence_attestation_duties_to_be_serves_orders(dv')
    {
        lemma_inv_none_latest_served_duty_implies_none_current_att_duty_dv_next(dv, e, dv');
        lemma_inv_current_att_duty_is_either_none_or_latest_served_duty_dv_next(dv, e, dv');
        lemma_inv_not_none_current_att_duty_is_latest_served_att_duty_dv_next(dv, e, dv');        
        lemma_inv_is_sequence_attestation_duties_to_be_serves_orders_dv_next(dv, e, dv');                
        // lemma_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_dv_next(dv, e, dv');
        // lemma_inv_strictly_increasing_queue_of_att_duties_dv_next(dv, e, dv');
        // lemma_inv_queued_att_duty_is_higher_than_latest_served_att_duty_dv_next(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_invs_8_18_helper_2(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_no_queued_att_duty_if_latest_served_att_duty_is_none(dv')
    ensures inv_strictly_increasing_queue_of_att_duties(dv')
    ensures inv_queued_att_duty_is_higher_than_latest_served_att_duty(dv')
    {
        lemma_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_dv_next(dv, e, dv');
        lemma_inv_strictly_increasing_queue_of_att_duties_dv_next(dv, e, dv');
        lemma_inv_queued_att_duty_is_higher_than_latest_served_att_duty_dv_next(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_invs_8_18(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_8_18(dv')
    {
        lemma_ind_inv_dv_next_invs_8_18_helper_1(dv, e, dv');
        lemma_ind_inv_dv_next_invs_8_18_helper_2(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_invs_19_26_helper_1(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_no_duplicated_att_duties(dv')        
    ensures concl_unchanged_dvn_seq_of_att_duties(dv, dv')
    ensures inv_every_att_duty_before_dvn_att_index_was_delivered(dv')
    ensures inv_no_active_consensus_instance_before_receiving_att_duty(dv')
    {
        lemma_inv_no_duplicated_att_duties_dv_next(dv, e, dv');
        lemma_concl_unchanged_dvn_seq_of_att_duties_dv_next(dv, e, dv');
        lemma_inv_every_att_duty_before_dvn_att_index_was_delivered_dv_next(dv, e, dv');        
        lemma_inv_no_active_consensus_instance_before_receiving_att_duty_dv_next(dv, e, dv');                
        // lemma_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_dv_next(dv, e, dv');                
        // lemma_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_dv_next(dv, e, dv');    
        // lemma_inv_consensus_instances_only_for_rcvd_duties_dv_next(dv, e, dv');    
    }

    lemma lemma_ind_inv_dv_next_invs_19_26_helper_2(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty(dv')        
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty(dv')
    ensures inv_consensus_instances_only_for_rcvd_duties(dv')
    {
        lemma_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_dv_next(dv, e, dv');                
        lemma_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_dv_next(dv, e, dv');    
        lemma_inv_consensus_instances_only_for_rcvd_duties_dv_next(dv, e, dv');    
    }

    lemma lemma_ind_inv_dv_next_invs_19_26(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_19_26(dv')        
    {
        lemma_ind_inv_dv_next_invs_19_26_helper_1(dv, e, dv');
        lemma_ind_inv_dv_next_invs_19_26_helper_2(dv, e, dv');
    }

    lemma lemma_ind_inv_invs_dv_next_4_helper1(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties(dv') 
    ensures inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred(dv')
    ensures inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k(dv')
    {
        lemma_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_dv_next(dv, e, dv');    
        lemma_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_dv_next(dv, e, dv');  
        lemma_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_dv_next(dv, e, dv');          
    }

    lemma lemma_ind_inv_invs_dv_next_4_helper2(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db(dv') 
    ensures inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist(dv')
    ensures inv_construct_signed_attestation_signature_assumptions_helper(dv')
    {       
        lemma_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_dv_next(dv, e, dv');  
        lemma_inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_dv_next(dv, e, dv');  
        lemma_inv_construct_signed_attestation_signature_assumptions_helper_dv_next(dv, e, dv');  
        // lemma_inv_all_in_transit_messages_were_sent_dv_next(dv, e, dv');  
        // lemma_inv_rcvd_attn_shares_are_from_sent_messages_dv_next(dv, e, dv');  
        // IndInv3.lemma_inv_33(dv, e, dv');
    }

    lemma lemma_ind_inv_invs_dv_next_4_helper3(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_all_in_transit_messages_were_sent(dv') 
    ensures inv_rcvd_attn_shares_are_from_sent_messages(dv')
    ensures IndInv3.inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper(dv')
    {               
        lemma_inv_all_in_transit_messages_were_sent_dv_next(dv, e, dv');  
        lemma_inv_rcvd_attn_shares_are_from_sent_messages_dv_next(dv, e, dv');  
        IndInv3.lemma_inv_33(dv, e, dv');
    }

    lemma lemma_ind_inv_invs_dv_next_4(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_27_37(dv') 
    {
        lemma_ind_inv_invs_dv_next_4_helper1(dv, e, dv');
        lemma_ind_inv_invs_dv_next_4_helper2(dv, e, dv');
        lemma_ind_inv_invs_dv_next_4_helper3(dv, e, dv');
    }

    lemma lemma_ind_inv_implies_intermediate_steps_helper_1(dv: DVState)
    requires ind_inv(dv)
    ensures concl_next_att_duty_is_higher_than_current_att_duty(dv)
    ensures concl_next_att_duty_is_higher_than_latest_served_att_duty(dv)
    ensures concl_future_att_duty_is_higher_than_rcvd_att_duty(dv)
    ensures concl_future_att_duty_is_higher_than_queued_att_duty(dv)
    ensures concl_slot_of_active_consensus_instance_is_lower_than_slot_of_queued_att_duty(dv)    
    {    
        lemma_concl_next_att_duty_is_higher_than_current_att_duty_ind_inv(dv);
        lemma_concl_next_att_duty_is_higher_than_latest_served_att_duty_ind_inv(dv);
        lemma_concl_future_att_duty_is_higher_than_rcvd_att_duty_ind_inv(dv);
        lemma_concl_future_att_duty_is_higher_than_queued_att_duty_ind_inv(dv);
        lemma_concl_slot_of_active_consensus_instance_is_lower_than_slot_of_queued_att_duty_ind_inv(dv);  
    }

    lemma lemma_ind_inv_implies_intermediate_steps_helper_2(dv: DVState)
    requires ind_inv(dv)  
    ensures inv_queued_att_duty_is_rcvd_duty0(dv)
    ensures inv_queued_att_duty_is_rcvd_duty1(dv)   
    ensures inv_queued_att_duty_is_rcvd_duty3(dv)    
    ensures construct_signed_attestation_signature_assumptions_helper(
                dv.construct_signed_attestation_signature,
                dv.dv_pubkey,
                dv.all_nodes)  
    {    
        lemma_inv_queued_att_duty_is_rcvd_duty0_ind_inv(dv);
        lemma_inv_queued_att_duty_is_rcvd_duty1_ind_inv(dv);
        lemma_inv_queued_att_duty_is_rcvd_duty3_ind_inv(dv);      
        lemma_construct_signed_attestation_signature_assumptions_helper(dv);       
    }

    lemma lemma_ind_inv_implies_intermediate_steps_helper_3(dv: DVState)
    requires ind_inv(dv)  
    ensures inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(dv)  
    ensures is_sequence_attestation_duties_to_be_served_orderd(dv)
    ensures inv_attestation_duty_queue_is_ordered(dv)
    ensures inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(dv)
    ensures pred_inv_current_latest_attestation_duty_match(dv)
    ensures pred_rcvd_attestation_shares_is_in_all_messages_sent(dv)
    {    
        lemma_inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(dv);
        lemma_inv_attestation_duty_queue_is_ordered(dv);
        lemma_inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(dv);
        lemma_pred_inv_current_latest_attestation_duty_match(dv);
        lemma_inv_rcvd_attn_shares_are_from_sent_messages_pred_rcvd_attestation_shares_is_in_all_messages_sent(dv);
    }

    lemma lemma_ind_inv_implies_intermediate_steps_helper_4(dv: DVState)
    requires ind_inv(dv)  
    ensures lemma_pred_4_1_g_iii_precond(dv)
    ensures lemma_pred_4_1_b_new_precond(dv)    
    {   
        lemma_ind_inv_implies_intermediate_steps_helper_1(dv);
        lemma_ind_inv_implies_intermediate_steps_helper_2(dv);
        lemma_ind_inv_implies_intermediate_steps_helper_3(dv);        
    }

    lemma lemma_ind_inv_implies_intermediate_steps(dv: DVState)
    requires ind_inv(dv)
    ensures concl_next_att_duty_is_higher_than_current_att_duty(dv)
    ensures concl_next_att_duty_is_higher_than_latest_served_att_duty(dv)
    ensures concl_future_att_duty_is_higher_than_rcvd_att_duty(dv)
    ensures concl_future_att_duty_is_higher_than_queued_att_duty(dv)
    ensures concl_slot_of_active_consensus_instance_is_lower_than_slot_of_queued_att_duty(dv)    
    ensures inv_queued_att_duty_is_rcvd_duty0(dv)
    ensures inv_queued_att_duty_is_rcvd_duty1(dv)   
    ensures inv_queued_att_duty_is_rcvd_duty3(dv)    
    ensures construct_signed_attestation_signature_assumptions_helper(
                dv.construct_signed_attestation_signature,
                dv.dv_pubkey,
                dv.all_nodes)  
    ensures inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(dv)   
    ensures is_sequence_attestation_duties_to_be_served_orderd(dv)     
    ensures inv_attestation_duty_queue_is_ordered(dv)
    ensures inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(dv)
    ensures pred_inv_current_latest_attestation_duty_match(dv)
    ensures pred_rcvd_attestation_shares_is_in_all_messages_sent(dv)
    ensures lemma_pred_4_1_g_iii_precond(dv)
    ensures lemma_pred_4_1_b_new_precond(dv)
    {   
        lemma_ind_inv_implies_intermediate_steps_helper_1(dv); 
        lemma_ind_inv_implies_intermediate_steps_helper_2(dv);
        lemma_ind_inv_implies_intermediate_steps_helper_3(dv);
        lemma_ind_inv_implies_intermediate_steps_helper_4(dv);
    }
   
    lemma lemma_ind_inv_dv_next_inv_46_b(dv: DVState, e: DV.Event, dv': DVState)  
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')       
    requires ind_inv(dv)
    ensures inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv')
    {
        lemma_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_inv_active_attestation_consensus_instances_predicate_is_in_att_slashing_db_hist(dv);
        assert inv_active_attestation_consensus_instances_predicate_is_in_att_slashing_db_hist(dv);

        lemma_inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(dv);
        assert inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(dv);

        lemma_ind_inv_implies_intermediate_steps(dv);
        assert inv_queued_att_duty_is_rcvd_duty3(dv);


        assert && inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv)
               && inv_quorum_constraints(dv)
               && inv_queued_att_duty_is_rcvd_duty3(dv)
               && inv_only_dv_construct_signed_attestation_signature(dv)    
               && IndInv3.inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper(dv)  
               && inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(dv)
               && inv_active_attestation_consensus_instances_predicate_is_in_att_slashing_db_hist(dv)
               ;

        lemma_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv, e, dv');    
        assert inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv');
    }

    lemma lemma_ind_inv_dv_next_inv_pred_4_1_b(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures pred_4_1_b(dv')
    {
        lemma_ind_inv_implies_intermediate_steps(dv);
        assert construct_signed_attestation_signature_assumptions_helper(
                dv.construct_signed_attestation_signature,
                dv.dv_pubkey,
                dv.all_nodes);

        lemma_inv_all_in_transit_messages_were_sent_invNetwork(dv);
        assert invNetwork(dv);

        lemma_inv_rcvd_attn_shares_are_from_sent_messages_pred_rcvd_attestation_shares_is_in_all_messages_sent(dv);
        assert pred_rcvd_attestation_shares_is_in_all_messages_sent(dv);

        assert  && DV.NextEvent(dv, e, dv')
                && pred_4_1_b(dv)
                && construct_signed_attestation_signature_assumptions_helper(
                    dv.construct_signed_attestation_signature,
                    dv.dv_pubkey,
                    dv.all_nodes
                )
                && inv_only_dv_construct_signed_attestation_signature(dv)  
                && invNetwork(dv)
                && inv_quorum_constraints(dv)
                && pred_rcvd_attestation_shares_is_in_all_messages_sent(dv)
                ;

        
        lemma_pred_4_1_b(dv, e, dv');
        assert pred_4_1_b(dv');
    }

    lemma lemma_ind_inv_dv_next_inv_pred_4_1_f_a(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures pred_4_1_f_a(dv')
    {
        lemma_pred_4_1_f_a(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_inv_pred_4_1_g_i_for_dvc(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures pred_4_1_g_i_for_dvc(dv')
    {
        lemma_pred_4_1_f_g_for_dvc(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_inv_pred_4_1_g_i(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures pred_4_1_g_i(dv')
    {
        lemma_pred_4_1_f_g_i(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_inv_pred_4_1_f_b(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures pred_4_1_f_b(dv')
    {
        lemma_pred_4_1_f_b(dv, e, dv');
    }

    predicate invs_other_properties_1(dv: DVState)       
    {                
        && inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv)
        && pred_4_1_b(dv) 
        && pred_4_1_f_a(dv)    
        && pred_4_1_g_i_for_dvc(dv)
        && pred_4_1_g_i(dv)
        
    }

    lemma lemma_ind_inv_dv_next_invs_other_properties_1(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_other_properties_1(dv')
    {
        lemma_ind_inv_dv_next_inv_46_b(dv, e, dv');  
        lemma_ind_inv_dv_next_inv_pred_4_1_b(dv, e, dv');             
        lemma_ind_inv_dv_next_inv_pred_4_1_f_a(dv, e, dv');       
        lemma_ind_inv_dv_next_inv_pred_4_1_g_i_for_dvc(dv, e, dv');  
        lemma_ind_inv_dv_next_inv_pred_4_1_g_i(dv, e, dv');   
    }

    lemma lemma_ind_inv_dv_next_inv_invNetwork(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invNetwork(dv')
    {
        lemma_inv_all_in_transit_messages_were_sent_dv_next(dv, e, dv');
        lemma_inv_all_in_transit_messages_were_sent_invNetwork(dv');
    }

    lemma lemma_ind_inv_dv_next_inv_38(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_attestation_shares_to_broadcast_are_sent_messages(dv')
    {
        lemma_ind_inv_implies_intermediate_steps(dv);
        assert inv_queued_att_duty_is_rcvd_duty3(dv);
        lemma_inv_attestation_shares_to_broadcast_are_sent_messages_dv_next(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_inv_pred_4_1_g_iii_a(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures pred_4_1_g_iii_a(dv')
    {
        lemma_pred_4_1_g_iii_a(dv, e, dv');
    }

    predicate invs_other_properties_2(dv: DVState)       
    {                    
        && pred_4_1_f_b(dv) 
        && invNetwork(dv)
        && inv_attestation_shares_to_broadcast_are_sent_messages(dv)
        && inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(dv)
    }

    lemma lemma_ind_inv_dv_next_invs_other_properties_2(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_other_properties_2(dv')
    {
        lemma_pred_4_1_f_b(dv, e, dv');
        lemma_ind_inv_dv_next_inv_invNetwork(dv, e, dv');
        lemma_ind_inv_dv_next_inv_38(dv, e, dv');
        lemma_inv_attestation_shares_to_broadcast_are_sent_messages_inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(dv');
    }

    lemma lemma_pred_4_1_g_iii_ind_inv(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )
    requires NextEvent.requires(dv, event, dv')
    requires NextEvent(dv, event, dv')
    requires ind_inv(dv)
    ensures pred_4_1_g_iii(dv')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dv);
        assert lemma_pred_4_1_g_iii_precond(dv);
        lemma_pred_4_1_g_iii(dv, event, dv');
    }

    predicate invs_other_properties_3(dv: DVState)       
    {                
        && pred_4_1_g_iii_a(dv)        
        && pred_4_1_g_iii_c(dv)
        && pred_4_1_g_iii_a_a(dv)        
        && pred_4_1_c(dv)                     
    }
    
    lemma lemma_ind_inv_dv_next_invs_other_properties_3(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_other_properties_3(dv')
    {        
        lemma_ind_inv_dv_next_inv_pred_4_1_g_iii_a(dv, e, dv');
        lemma_pred_4_1_g_iii_c_dv_next(dv, e, dv');
        lemma_pred_4_1_g_iii_a_a(dv, e, dv');
        lemma_ind_inv_implies_intermediate_steps(dv);
        lemma_pred_4_1_c(dv, e, dv');
    }
    
    predicate invs_other_properties_4(dv: DVState)       
    {
        && inv_attestation_duty_queue_is_ordered_3(dv)
        && inv_attestation_duty_queue_is_ordered_4(dv)
    }

    lemma lemma_ind_inv_dv_next_invs_other_properties_4(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_other_properties_4(dv')
    {        
        lemma_inv_attestation_duty_queue_is_ordered_3(dv, e, dv');
        lemma_inv_attestation_duty_queue_is_ordered_4(dv, e, dv');        
    }

    lemma lemma_ind_inv_dv_next_inv_pred_4_1_g_iii_b(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures pred_4_1_g_iii_b(dv')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dv);
        lemma_4_1_g_iii_b(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_inv_pred_4_1_g_b_new(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures pred_4_1_g_b_new(dv')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dv);
        lemma_pred_4_1_b_new(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_inv_g_d_a(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_g_d_a(dv')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dv);
        lemma_inv_g_d_a(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_inv_g_d_b(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_g_d_b(dv')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dv);
        lemma_inv_g_d_b(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_inv_g_a_ii_a(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_g_a_ii_a(dv')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dv);
        lemma_inv_g_a_ii_a(dv, e, dv');
    }



    lemma lemma_ind_inv_dv_next_invs_other_properties_5(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_other_properties_5(dv')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dv);
        
        lemma_4_1_g_iii_b(dv, e, dv');
        lemma_pred_4_1_b_new(dv, e, dv');
        lemma_inv_g_d_a(dv, e, dv');
        lemma_inv_g_d_b(dv, e, dv');        
        lemma_inv_g_a_ii_a(dv, e, dv');
    }

    
    predicate invs_other_properties_5(dv: DVState)       
    {                
        && pred_4_1_g_iii_b(dv)    
        && pred_4_1_g_b_new(dv)    
        && inv_g_d_a(dv)
        && inv_g_d_b(dv)  
        && inv_g_a_ii_a(dv)        
    }
    
    predicate invs_other_properties_6(dv: DVState)       
    {                
        && inv_g_a_iii(dv)
        && inv_g_a_iv_a(dv)
        && pred_4_1_g_iii(dv)        
    }

    predicate invs_other_properties_7(dv: DVState)       
    {                
        && inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv)
        && inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv)
    }

          
    lemma lemma_ind_inv_dv_next_invs_other_properties_6(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_other_properties_6(dv')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dv);

        lemma_inv_g_a_iii(dv, e, dv');
        lemma_inv_g_a_iv_a(dv, e, dv');
        lemma_pred_4_1_g_iii(dv, e, dv');        
    }

    lemma lemma_ind_inv_dv_next_invs_other_properties_7(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_other_properties_7(dv')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dv);

        lemma_inv_46_a(dv, e, dv');
        lemma_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv, e, dv');
    }


    // Adding DV.NextEventPreCond(dv, e) makes this lemma too complicated for Dafny on my computer.
    // lemma lemma_ind_inv_dv_next_ind_inv_helper_1(dv: DVState, e: DV.Event, dv': DVState)       
    // requires DV.NextEventPreCond(dv, e)
    // requires DV.NextEvent(dv, e, dv')  
    // requires ind_inv(dv)
    // ensures invs_1_7(dv')
    // ensures invs_8_18(dv')
    // ensures invs_19_26(dv')
    // ensures invs_27_37(dv')
    // {
    //     lemma_ind_inv_dv_next_invs_1_7(dv, e, dv');
    //     lemma_ind_inv_dv_next_invs_8_18(dv, e, dv');
    //     lemma_ind_inv_dv_next_invs_19_26(dv, e, dv');
    //     lemma_ind_inv_invs_dv_next_4(dv, e, dv');         
    // }
    
    lemma lemma_ind_inv_dv_next_ind_inv_helper_1(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_1_7(dv')
    ensures invs_8_18(dv')
    {
        lemma_ind_inv_dv_next_invs_1_7(dv, e, dv');
        lemma_ind_inv_dv_next_invs_8_18(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_ind_inv_helper_2(dv: DVState, e: DV.Event, dv': DVState)  
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)    
    ensures invs_19_26(dv')
    ensures invs_27_37(dv')     
    {
        lemma_ind_inv_dv_next_invs_19_26(dv, e, dv');
        lemma_ind_inv_invs_dv_next_4(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_ind_inv_helper_3(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_other_properties_1(dv')
    ensures invs_other_properties_2(dv')
    ensures invs_other_properties_3(dv')
    ensures invs_other_properties_4(dv')    
    {        
        lemma_ind_inv_dv_next_invs_other_properties_1(dv, e, dv');       
        lemma_ind_inv_dv_next_invs_other_properties_2(dv, e, dv');  
        lemma_ind_inv_dv_next_invs_other_properties_3(dv, e, dv');            
        lemma_ind_inv_dv_next_invs_other_properties_4(dv, e, dv');                              
    }

    lemma lemma_ind_inv_dv_next_ind_inv_helper_4(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)    
    ensures invs_other_properties_5(dv')
    ensures invs_other_properties_6(dv')
    ensures invs_other_properties_7(dv')
    {                 
        lemma_ind_inv_dv_next_invs_other_properties_5(dv, e, dv');            
        lemma_ind_inv_dv_next_invs_other_properties_6(dv, e, dv');            
        lemma_ind_inv_dv_next_invs_other_properties_7(dv, e, dv');            
    }

    lemma lemma_ind_inv_dv_next_ind_inv_helper_a(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv) 
    ensures invs_1_7(dv')
    ensures invs_8_18(dv')   
    ensures invs_19_26(dv')
    ensures invs_27_37(dv')  
    {
        lemma_ind_inv_dv_next_ind_inv_helper_1(dv, e, dv');                          
        lemma_ind_inv_dv_next_ind_inv_helper_2(dv, e, dv');    
    }

    lemma lemma_ind_inv_dv_next_ind_inv_helper_b(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv) 
    ensures invs_other_properties_1(dv')    
    ensures invs_other_properties_2(dv')    
    ensures invs_other_properties_3(dv')    
    ensures invs_other_properties_4(dv')    
    ensures invs_other_properties_5(dv')    
    ensures invs_other_properties_6(dv')  
    ensures invs_other_properties_7(dv')  
    {
        lemma_ind_inv_dv_next_ind_inv_helper_3(dv, e, dv');     
        lemma_ind_inv_dv_next_ind_inv_helper_4(dv, e, dv');            
    }

    lemma lemma_ind_inv_dv_next_ind_inv_helper(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv) 
    ensures invs_1_7(dv')
    ensures invs_8_18(dv')   
    ensures invs_19_26(dv')
    ensures invs_27_37(dv')  
    ensures invs_other_properties_1(dv')    
    ensures invs_other_properties_2(dv')    
    ensures invs_other_properties_3(dv')    
    ensures invs_other_properties_4(dv')    
    ensures invs_other_properties_5(dv')    
    ensures invs_other_properties_6(dv')    
    ensures invs_other_properties_7(dv')    
    {   
        lemma_ind_inv_dv_next_ind_inv_helper_a(dv, e, dv');
        lemma_ind_inv_dv_next_ind_inv_helper_b(dv, e, dv');                
    }

    lemma lemma_ind_inv_dv_next_ind_inv(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)    
    ensures ind_inv(dv')    
    {   
        lemma_ind_inv_dv_next_ind_inv_helper(dv, e, dv');                          
        lemma_inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_next_honest(dv, e, dv');       
    }

    lemma lemma_ind_inv_dv_ind(dv: DVState, dv': DVState)       
    requires DV.NextPreCond(dv)
    requires DV.Next(dv, dv')  
    requires ind_inv(dv)    
    ensures ind_inv(dv')  
    ensures DV.NextPreCond(dv')
    {
        var e :|
            && validEvent(dv, e)
            && NextEvent(dv, e, dv');

        lemma_ind_inv_dv_next_ind_inv(dv, e, dv');
        lemma_NextPreCond(dv');
    }      

    predicate non_slashable_attestations(
        dv: DVState
    )
    {
        forall a: Attestation, a': Attestation
                | 
                && a in dv.all_attestations_created
                && is_valid_attestation(a, dv.dv_pubkey)
                && a' in dv.all_attestations_created
                && is_valid_attestation(a', dv.dv_pubkey)     
                ::
                && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
                && !is_slashable_attestation_data_eth_spec(a'.data, a.data)
    }

    lemma lemma_ind_inv_4_1_general(dv: DVState)
    requires ind_inv(dv)    
    ensures non_slashable_attestations(dv)
    {   
        lemma_ind_inv_implies_intermediate_steps(dv);

        forall a: Attestation, a': Attestation
                    | 
                    && a in dv.all_attestations_created
                    && is_valid_attestation(a, dv.dv_pubkey)
                    && a' in dv.all_attestations_created
                    && is_valid_attestation(a', dv.dv_pubkey)     
        ensures && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
                && !is_slashable_attestation_data_eth_spec(a'.data, a.data);
        {
            assert 
            && inv_quorum_constraints(dv)
            && inv_unchanged_honesty(dv)
            && pred_4_1_b(dv)
            && pred_4_1_c(dv)
            && pred_4_1_f_a(dv)    
            && pred_4_1_g_i(dv)
            && pred_4_1_g_iii(dv)
            && a in dv.all_attestations_created
            && is_valid_attestation(a, dv.dv_pubkey)
            && a' in dv.all_attestations_created
            && is_valid_attestation(a', dv.dv_pubkey)
            && inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv)
            && inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv)
            && inv_queued_att_duty_is_rcvd_duty0(dv)
            && inv_queued_att_duty_is_rcvd_duty1(dv)
            ;
            lemma_4_1_general(dv, a, a');
        }
    }

}