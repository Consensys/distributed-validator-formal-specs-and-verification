include "../../../common/block_proposer/block_types.dfy"
include "../../../common/block_proposer/block_common_functions.dfy"
include "../../../common/block_proposer/block_signing_functions.dfy"
include "../../../specs/consensus/block_consensus.dfy"
include "../../../specs/network/block_network.dfy"
include "../../../specs/dv/dv_block_proposer.dfy"
include "../common/dvc_block_proposer_instrumented.dfy"
include "../../common/helper_sets_lemmas.dfy"
include "../common/block_dvc_spec_axioms.dfy"
include "inv.dfy"


module Block_Ind_Inv_With_Empty_Initial_Block_Slashing_DB
{
    import opened Block_Types 
    import opened Block_Common_Functions
    import opened Block_Signing_Functions
    import opened Block_Consensus_Spec
    import opened Block_Network_Spec
    import opened DVC_Block_Proposer_Spec_Instr
    import opened DV_Block_Proposer_Spec
    import opened Block_Inv_With_Empty_Initial_Block_Slashing_DB

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
        &&  inv_unchanged_paras_of_consensus_instances(dv)
        &&  inv_only_dv_construct_complete_signing_functions(dv)
        &&  inv_current_proposer_duty_is_rcvd_duty(dv)
        &&  inv_latest_served_duty_is_rcvd_duty(dv)
    }

    predicate invs_group_2(dv: DVState)       
    {        
        &&  inv_none_latest_served_duty_implies_none_current_proposer_duty(dv)   
        &&  inv_current_proposer_duty_is_either_none_or_latest_served_duty(dv)  
        &&  inv_available_current_proposer_duty_is_latest_served_proposer_duty(dv) 
    }

    predicate invs_group_3(dv: DVState)       
    {        
        &&  inv_no_duplicated_proposer_duties(dv)           
        &&  inv_every_proposer_duty_before_dvn_proposer_index_was_delivered(dv) 
        &&  inv_no_active_consensus_instance_before_receiving_a_proposer_duty(dv)              
    }

    predicate invs_group_4(dv: DVState)       
    {        
        &&  inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty(dv)  
        &&  inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty(dv)          
        &&  inv_consensus_instances_only_for_rcvd_duties(dv)  
        &&  inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty(dv)
    }

    predicate invs_group_5(dv: DVState)       
    {                
        &&  inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties(dv)  
        &&  inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate(dv)  
        &&  inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k(dv)          
    }

    predicate invs_group_6(dv: DVState)       
    {                
        &&  inv_every_db_in_block_slashing_db_hist_is_subset_of_block_slashing_db(dv)  
        &&  inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist(dv)

        // &&  inv_construct_signed_attestation_signature_assumptions_helper(dv)        
    }

    predicate invs_group_7(dv: DVState)       
    {                
        &&  inv_all_in_transit_messages_were_sent(dv)
        &&  inv_rcvd_block_shares_are_from_sent_messages(dv)
        &&  inv_slots_for_sent_validity_predicate_are_stored_in_block_slashing_db_hist(dv)
    }
    
    predicate invs_group_8(dv: DVState)       
    {   
        && inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(dv) 
        && inv_decided_value_of_consensus_instance_is_decided_by_quorum(dv)    
        && inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(dv)
        && inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(dv)
    }

    predicate invs_group_9(dv: DVState)       
    {                    
        && inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(dv) 
        && invNetwork(dv)
        && inv_block_shares_to_broadcast_are_sent_messages(dv)

        // Move to intermediate steps
        && inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(dv)

        
    }

    predicate invs_group_10(dv: DVState)       
    {   
        && inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv)        
        && inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist(dv) 
        && inv_block_of_in_transit_block_share_is_decided_value(dv)                     

        // Move to intermediate steps
        && inv_available_current_proposer_duty_is_from_dv_seq_of_proposer_duties(dv)                 
        
    }
    
    predicate invs_group_11(dv: DVState)       
    {             
        && inv_slot_in_future_beacon_block_is_correct(dv)  
        && inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv(dv)
        && inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties(dv)
        && inv_unique_rcvd_proposer_duty_per_slot(dv)
    }
    
    predicate invs_group_12(dv: DVState)       
    {   
        && inv_consensus_instance_isConditionForSafetyTrue(dv)
        && inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty(dv)
        && inv_sent_validity_predicate_only_for_slots_stored_in_block_slashing_db_hist(dv)
        && inv_all_validity_predicates_are_stored_in_block_slashing_db_hist(dv)
        
    }

    predicate invs_group_13(dv: DVState)       
    {   
        && inv_unchanged_dvc_rs_pubkey(dv)
        && inv_all_created_signed_beacon_blocks_are_valid(dv)
        && inv_complete_block_is_created_with_shares_from_quorum(dv)
        && inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block(dv)

        // Move to intermediate steps
        // && inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty(dv)
    }

    predicate invs_group_14(dv: DVState)       
    {   
        && inv_seq_of_proposer_duties_is_ordered(dv)
        && inv_block_shares_to_broadcast_is_tracked_in_block_slashing_db(dv)
        && inv_block_of_block_shares_is_known(dv)
        && inv_slot_of_consensus_instance_is_up_to_slot_of_latest_proposer_duty(dv)
        && inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_for_lower_slots(dv)
    }

    predicate invs_group_15(dv: DVState)       
    {   
        && inv_none_latest_proposer_duty_implies_emply_block_slashing_db(dv)
        && inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty(dv)
        && inv_at_most_submitted_signed_beacon_block_for_every_slot(dv)
    }
}