include "../../../common/commons.dfy"
include "../common/attestation_creation_instrumented.dfy"
include "../../../specs/consensus/consensus.dfy"
include "../../../specs/network/network.dfy"
include "../../../specs/dv/dv_attestation_creation.dfy"
include "inv.dfy"


module Att_Ind_Inv_With_Empty_Init_Att_Slashing_DB
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB

    predicate ind_inv(dv: DVState)       
    {
        && invs_group_1(dv)        
        && invs_group_2(dv)
        && invs_group_3(dv)
        && invs_group_4(dv)
        && invs_group_5(dv)        
        && invs_group_6(dv)
        && invs_group_7(dv)
        && invs_group_8(dv)                
        && invs_group_9(dv)
        && invs_group_10(dv)
        && invs_group_11(dv)
        && invs_group_12(dv)
        && invs_group_13(dv)
        && invs_group_14(dv)
        && invs_group_15(dv)        
    }

    predicate invs_group_1(dv: DVState)       
    {
        &&  inv_quorum_constraints(dv)
        &&  inv_unchanged_honesty(dv)
        &&  inv_only_dv_construct_signed_attestation_signature(dv)
        &&  inv_queued_att_duty_is_dvn_seq_of_att_duty(dv)
        &&  inv_queued_att_duty_is_rcvd_duty(dv)
        &&  inv_current_att_duty_is_rcvd_duty(dv)
        &&  inv_latest_served_duty_is_rcvd_duty(dv)
    }

    predicate invs_group_2(dv: DVState)       
    {        
        &&  inv_none_latest_served_duty_implies_none_current_att_duty(dv)   
        &&  inv_current_att_duty_is_either_none_or_latest_served_duty(dv)  
        &&  inv_not_none_current_att_duty_is_latest_served_att_duty(dv) 
        &&  inv_is_sequence_attestation_duties_to_be_serves_orders(dv)              
    }

    predicate invs_group_3(dv: DVState)       
    {        
        &&  inv_no_queued_att_duty_if_latest_served_att_duty_is_none(dv)  
        &&  inv_strictly_increasing_queue_of_att_duties(dv)  
        &&  inv_queued_att_duty_is_higher_than_latest_served_att_duty(dv)  
    }

    predicate invs_group_4(dv: DVState)       
    {        
        &&  inv_no_duplicated_att_duties(dv)           
        &&  inv_every_att_duty_before_dvn_att_index_was_delivered(dv) 
        &&  inv_no_active_consensus_instance_before_receiving_att_duty(dv)              
    }

    predicate invs_group_5(dv: DVState)       
    {        
        &&  inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty(dv)  
        &&  inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty(dv)          
        &&  inv_consensus_instances_only_for_rcvd_duties(dv)  
    }

    predicate invs_group_6(dv: DVState)       
    {                
        &&  inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties(dv)  
        &&  inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred(dv)  
        &&  inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k(dv)          
    }

    predicate invs_group_7(dv: DVState)       
    {                
        &&  inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db(dv)  
        &&  inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist(dv)
        &&  inv_construct_signed_attestation_signature_assumptions_helper(dv)        
    }

    predicate invs_group_8(dv: DVState)       
    {                
        &&  inv_all_in_transit_messages_were_sent(dv)
        &&  inv_rcvd_attn_shares_are_from_sent_messages(dv)
        &&  inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper(dv)
    }
    
    predicate invs_group_9(dv: DVState)       
    {                
        && inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv)
        && pred_4_1_b(dv) 
        && pred_4_1_f_a(dv)    
        && pred_4_1_g_i_for_dvc(dv)
        && pred_4_1_g_i(dv)
        
    }

    predicate invs_group_10(dv: DVState)       
    {                    
        && pred_4_1_f_b(dv) 
        && invNetwork(dv)
        && inv_attestation_shares_to_broadcast_are_sent_messages(dv)
        && inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(dv)
    }

    predicate invs_group_11(dv: DVState)       
    {                
        && pred_4_1_g_iii_a(dv)        
        && pred_4_1_g_iii_c(dv)
        && pred_4_1_g_iii_a_a(dv)        
        && pred_4_1_c(dv)                     
    }
    
    predicate invs_group_12(dv: DVState)       
    {
        && inv_attestation_duty_queue_is_ordered_3(dv)
        && inv_attestation_duty_queue_is_ordered_4(dv)
    }

    predicate invs_group_13(dv: DVState)       
    {                
        && pred_4_1_g_iii_b(dv)    
        && pred_4_1_g_b_new(dv)    
        && inv_g_d_a(dv)
        && inv_g_d_b(dv)  
        && inv_g_a_ii_a(dv)        
    }
    
    predicate invs_group_14(dv: DVState)       
    {                
        && inv_g_a_iii(dv)
        && inv_g_a_iv_a(dv)
        && pred_4_1_g_iii(dv)        
    }

    predicate invs_group_15(dv: DVState)       
    {                
        && inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv)
        && inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv)
    }
}