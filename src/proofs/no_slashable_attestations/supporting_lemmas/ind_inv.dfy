include "../../../common/commons.dfy"
include "../common/dvc_attestation_creation_instrumented.dfy"
include "../../../specs/dv/dv_attestation_creation.dfy"
include "inv.dfy"


module Att_Ind_Inv_With_Empty_Init_Att_Slashing_DB
{
    import opened Types 
    import opened Att_DVC_Spec
    import opened Att_DV
    import opened Att_DV_Assumptions
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB

    predicate ind_inv(dv: Att_DVState)       
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
    }

    predicate invs_group_1(dv: Att_DVState)       
    {
        &&  inv_all_honest_nodes_is_a_quorum(dv)
        &&  inv_unchanged_paras_of_consensus_instances(dv)
        &&  inv_only_dv_construct_signed_attestation_signature(dv)
        &&  inv_current_att_duty_is_rcvd_duty(dv)
        &&  inv_latest_att_duty_is_rcvd_duty(dv)
    }

    predicate invs_group_2(dv: Att_DVState)       
    {        
        &&  inv_none_latest_att_duty_implies_none_current_att_duty(dv)   
        &&  inv_current_att_duty_is_either_none_or_latest_att_duty(dv)  
        &&  inv_available_current_att_duty_is_latest_att_duty(dv) 
        &&  inv_the_sequence_of_att_duties_is_in_order_of_slots(dv.sequence_attestation_duties_to_be_served)              
    }

    predicate invs_group_3(dv: Att_DVState)       
    {        
        &&  inv_no_duplicated_att_duties(dv)           
        &&  inv_every_att_duty_before_dvn_att_index_was_delivered(dv) 
        &&  inv_no_active_consensus_instances_before_the_first_att_duty_was_received(dv)              
    }

    predicate invs_group_4(dv: Att_DVState)       
    {        
        &&  inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty(dv)  
        &&  inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance(dv)          
        &&  inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k(dv)  
        &&  inv_rcvd_att_duties_are_from_dv_seq_of_att_duties(dv)
    }

    predicate invs_group_5(dv: Att_DVState)       
    {                
        &&  inv_slashing_db_hist_keeps_track_only_of_rcvd_att_duties(dv)  
        &&  inv_exist_a_db_in_slashing_db_hist_and_an_att_duty_for_every_validity_predicate(dv)  
        &&  inv_current_validity_predicate_for_slot_k_is_stored_in_slashing_db_hist_k(dv)          
    }

    predicate invs_group_6(dv: Att_DVState)       
    {                
        &&  inv_every_db_in_slashing_db_hist_is_a_subset_of_att_slashing_db(dv)  
        &&  inv_active_att_consensus_instances_are_tracked_in_slashing_db_hist(dv)
        &&  inv_construct_signed_attestation_signature_assumptions(dv)        
    }

    predicate invs_group_7(dv: Att_DVState)       
    {                
        &&  inv_all_in_transit_messages_were_sent(dv)
        &&  inv_rcvd_att_shares_are_from_sent_messages(dv)
        &&  inv_slots_for_sent_validity_predicates_are_stored_in_slashing_db_hist(dv)
    }
    
    predicate invs_group_8(dv: Att_DVState)       
    {                
        && inv_all_validity_predicates_are_stored_in_slashing_db_hist(dv)
        && inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(dv) 
        && inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(dv)    
        && inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(dv)
        && inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(dv)
        
    }

    predicate invs_group_9(dv: Att_DVState)       
    {                    
        && inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(dv) 
        && inv_in_transit_messages_are_in_allMessagesSent(dv)
        && inv_attestation_shares_to_broadcast_are_sent_messages(dv)
        && inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(dv)
    }

    predicate invs_group_10(dv: Att_DVState)       
    {                
        && inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_slashing_db_hist(dv)        
        && inv_latest_att_duty_is_from_dv_seq_of_att_duties(dv)
        && inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty(dv)        
        && inv_data_of_att_shares_are_decided_values(dv)                     
    }
    
    predicate invs_group_11(dv: Att_DVState)       
    {                
        && inv_future_decisions_known_by_dvc_are_decisions_of_quorums(dv)
        && inv_slots_in_future_decided_data_are_correct(dv)  
    }
    
    predicate invs_group_12(dv: Att_DVState)       
    {                
        && inv_sent_validity_predicates_are_only_for_slots_stored_in_slashing_db_hist(dv)
        && inv_all_validity_predicates_are_stored_in_slashing_db_hist(dv)
        && inv_every_consensus_instance_isConditionForSafetyTrue(dv)
        && inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties(dv)
        && inv_unique_rcvd_att_duty_per_slot(dv)
        && inv_no_rcvd_att_duties_are_higher_than_latest_att_duty(dv)
    }

    predicate invs_group_13(dv: Att_DVState)       
    {   
        && inv_every_decided_data_has_an_honest_witness(dv)
        && inv_all_created_attestations_are_valid(dv)
        && inv_an_attestation_is_created_based_on_shares_of_a_quorum(dv)
        && inv_unchanged_dvc_rs_pubkey(dv)
    }

    predicate invs_group_14(dv: Att_DVState)       
    {   
        && inv_the_sequence_of_att_duties_is_in_order_of_slots(dv.sequence_attestation_duties_to_be_served)
        && inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db(dv)
        && inv_sent_att_shares_have_corresponding_slashing_db_attestations(dv)
        && inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty(dv)
        && inv_db_of_vp_contains_all_data_of_sent_att_shares_with_lower_slots(dv)
    }
}