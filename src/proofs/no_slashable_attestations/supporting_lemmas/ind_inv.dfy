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
    }

    predicate invs_group_1(dv: DVState)       
    {
        &&  inv_quorum_constraints(dv)
        &&  inv_unchanged_paras_of_consensus_instances(dv)
        &&  inv_only_dv_construct_signed_attestation_signature(dv)
        &&  inv_current_att_duty_is_rcvd_duty(dv)
        &&  inv_latest_served_duty_is_rcvd_duty(dv)
    }

    predicate invs_group_2(dv: DVState)       
    {        
        &&  inv_none_latest_served_duty_implies_none_current_att_duty(dv)   
        &&  inv_current_att_duty_is_either_none_or_latest_served_duty(dv)  
        &&  inv_available_current_att_duty_is_latest_served_att_duty(dv) 
        &&  inv_is_sequence_attestation_duties_to_be_serves_orders(dv)              
    }

    predicate invs_group_3(dv: DVState)       
    {        
        &&  inv_no_duplicated_att_duties(dv)           
        &&  inv_every_att_duty_before_dvn_att_index_was_delivered(dv) 
        &&  inv_no_active_consensus_instance_before_receiving_an_att_duty(dv)              
    }

    predicate invs_group_4(dv: DVState)       
    {        
        &&  inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty(dv)  
        &&  inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty(dv)          
        &&  inv_consensus_instances_only_for_rcvd_duties(dv)  
        &&  inv_rcvd_att_duty_is_from_dv_seq_for_rcvd_att_duty(dv)
    }

    predicate invs_group_5(dv: DVState)       
    {                
        &&  inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties(dv)  
        &&  inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate(dv)  
        &&  inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k(dv)          
    }

    predicate invs_group_6(dv: DVState)       
    {                
        &&  inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db(dv)  
        &&  inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist(dv)
        &&  inv_construct_signed_attestation_signature_assumptions_helper(dv)        
    }

    predicate invs_group_7(dv: DVState)       
    {                
        &&  inv_all_in_transit_messages_were_sent(dv)
        &&  inv_rcvd_attn_shares_are_from_sent_messages(dv)
        &&  inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist(dv)
    }
    
    predicate invs_group_8(dv: DVState)       
    {                
        && inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv)
        && inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv) 
        && inv_decided_value_of_consensus_instance_is_decided_by_quorum(dv)    
        && inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(dv)
        && inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(dv)
        
    }

    predicate invs_group_9(dv: DVState)       
    {                    
        && inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(dv) 
        && invNetwork(dv)
        && inv_attestation_shares_to_broadcast_are_sent_messages(dv)
        && inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(dv)
    }

    predicate invs_group_10(dv: DVState)       
    {                
        && inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist(dv)        
        && inv_latest_attestation_duty_is_from_dv_seq_of_att_duties(dv)
        && inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a(dv)        
        && inv_data_of_att_share_is_decided_value(dv)                     
    }
    
    predicate invs_group_11(dv: DVState)       
    {                
        && inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv(dv)
        && inv_slot_in_future_decided_data_is_correct(dv)  
    }
    
    predicate invs_group_12(dv: DVState)       
    {                
        && inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv)
        && inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv)
        && inv_consensus_instances_are_isConditionForSafetyTrue(dv)
        && inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties(dv)
        && inv_unique_rcvd_att_duty_per_slot(dv)
        && inv_no_rcvd_att_duty_is_higher_than_latest_att_duty(dv)
    }

    predicate invs_group_13(dv: DVState)       
    {   
        && inv_decided_data_has_an_honest_witness(dv)
        && inv_all_created_attestations_are_valid(dv)
        && inv_attestation_is_created_with_shares_from_quorum(dv)
        && inv_unchanged_dvc_rs_pubkey(dv)
    }

    predicate invs_group_14(dv: DVState)       
    {   
        && inv_sequence_attestation_duties_to_be_served_ordered(dv)
        && inv_att_shares_to_broadcast_is_tracked_in_attestation_slashing_db(dv)
        && inv_data_of_att_shares_is_known(dv)
        && inv_slot_of_consensus_instance_is_up_to_slot_of_latest_attestation_duty(dv)
        && inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv)
    }
}