include "../../../common/commons.dfy"

include "../../../specs/consensus/consensus.dfy"
include "../../../specs/network/network.dfy"
include "../../../specs/dv/dv_block_proposer.dfy"
include "../common/dvc_block_proposer_instrumented.dfy"
include "../../common/helper_sets_lemmas.dfy"
include "../common/block_dvc_spec_axioms.dfy"
include "inv.dfy"


module Block_Ind_Inv_With_Empty_Initial_Block_Slashing_DB
{
    import opened Types 
    import opened CommonFunctions
    
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Block_Proposer_Spec_Instr
    import opened Block_Consensus_Engine_Instr
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
        &&  inv_all_honest_nodes_is_a_quorum(dv)
        &&  inv_nodes_in_consensus_instances_are_in_dv(dv)
        &&  inv_only_dv_construct_complete_signing_functions(dv)
        &&  inv_current_proposer_duty_is_a_rcvd_duty(dv)
        &&  inv_latest_served_duty_is_a_rcvd_duty(dv)
    }

    predicate invs_group_2(dv: DVState)       
    {        
        &&  inv_none_latest_proposer_duty_implies_none_current_proposer_duty(dv)   
        &&  inv_current_proposer_duty_is_either_none_or_latest_proposer_duty(dv)  
        &&  inv_available_current_proposer_duty_is_latest_proposer_duty(dv) 
    }

    predicate invs_group_3(dv: DVState)       
    {        
        &&  inv_no_duplicated_proposer_duties(dv)           
        &&  inv_every_proposer_duty_before_dv_index_next_proposer_duty_to_be_served_was_delivered(dv) 
        &&  inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none(dv)              
    }

    predicate invs_group_4(dv: DVState)       
    {        
        &&  inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty(dv)  
        &&  inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties(dv)          
        &&  inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k(dv)  
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
        &&  inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db(dv)  
        &&  inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist(dv)
    }

    predicate invs_group_7(dv: DVState)       
    {                
        // &&  inv_the_same_node_status_in_dv_and_ci(dv)
        &&  inv_all_in_transit_messages_were_sent(dv)
        &&  inv_rcvd_block_shares_are_from_sent_messages(dv)
        &&  inv_slots_for_sent_validity_predicates_are_stored_in_block_slashing_db_hist(dv)
    }
    
    predicate invs_group_8(dv: DVState)       
    {   
        && inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(dv) 
        && inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(dv)    
        && inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(dv)
        && inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(dv)
    }

    predicate invs_group_9(dv: DVState)       
    {                    
        && inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(dv) 
        && inv_in_transit_messages_are_in_allMessagesSent(dv)
        && inv_block_shares_to_broadcast_are_sent_messages(dv)

        // Move to intermediate steps
        && inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(dv)

        
    }

    predicate invs_group_10(dv: DVState)       
    {   
        && inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv)        
        && inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist(dv) 
        && inv_blocks_of_in_transit_block_shares_are_decided_values(dv)                     

        // Move to intermediate steps
        && inv_available_current_proposer_duty_is_from_dv_seq_of_proposer_duties(dv)                 
        
    }
    
    predicate invs_group_11(dv: DVState)       
    {             
        && inv_slots_in_future_decided_beacon_blocks_are_correct(dv)  
        && inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums(dv)
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
        && inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum(dv)
        && inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block(dv)

        // Move to intermediate steps
        // && inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty(dv)
    }

    predicate invs_group_14(dv: DVState)       
    {   
        && inv_seq_of_proposer_duties_is_ordered(dv)
        && inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db(dv)
        && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks(dv)
        && inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
        && inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv)
    }

    predicate invs_group_15(dv: DVState)       
    {   
        && inv_none_latest_proposer_duty_implies_emply_block_slashing_db(dv)
        && inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty(dv)
        && inv_at_most_one_submitted_signed_beacon_block_with_an_available_signing_root_for_every_slot(dv)
        && inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block(dv)
        && inv_none_latest_slashing_db_block_implies_emply_block_slashing_db(dv)
    }
}