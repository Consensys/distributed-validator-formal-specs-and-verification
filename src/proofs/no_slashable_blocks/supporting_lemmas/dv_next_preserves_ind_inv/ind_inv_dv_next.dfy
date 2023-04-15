include "../../../../common/block_proposer/block_types.dfy"
include "../../../../common/block_proposer/block_common_functions.dfy"
include "../../../../common/block_proposer/block_signing_functions.dfy"
include "../../common/dvc_block_proposer_instrumented.dfy"
include "../../common/block_dvc_spec_axioms.dfy"

include "../../../../specs/consensus/block_consensus.dfy"
include "../../../../specs/network/block_network.dfy"
include "../../../../specs/dv/dv_block_proposer.dfy"

include "invs_fnc_1.dfy"
include "invs_fnc_2.dfy"
include "invs_dv_next_1.dfy"
include "invs_dv_next_2.dfy"
include "invs_dv_next_3.dfy"
include "invs_dv_next_4.dfy"
include "invs_dv_next_5.dfy"

include "../inv.dfy"
include "../ind_inv.dfy"

include "proofs_intermediate_steps.dfy"

module Ind_Inv_DV_Next
{
    import opened Block_Types
    import opened Block_Signing_Functions
    import opened Block_Common_Functions
    import opened Block_Consensus_Spec
    import opened Block_Network_Spec
    import opened DVC_Block_Proposer_Spec_Instr
    import opened DVC_Block_Proposer_Spec_Axioms
    import opened Block_Inv_With_Empty_Initial_Block_Slashing_DB
    import opened Block_Ind_Inv_With_Empty_Initial_Block_Slashing_DB
    import opened DV_Block_Proposer_Spec    
    import opened Fnc_Invs_1
    import opened Fnc_Invs_2
    import opened Invs_DV_Next_1
    import opened Invs_DV_Next_2
    import opened Invs_DV_Next_3
    import opened Invs_DV_Next_4
    import opened Invs_DV_Next_5
    import opened Proofs_Intermediate_Steps
    

    lemma lem_ind_inv_dv_next_invs_group_1(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_1(dv')
    {    
        lem_inv_quorum_constraints_dv_next(dv, e, dv');
        lem_inv_unchanged_paras_of_consensus_instances_dv_next(dv, e, dv');
        lem_inv_only_dv_construct_complete_signing_functions_dv_next(dv, e, dv');
        lem_inv_current_proposer_duty_is_rcvd_duty_dv_next(dv, e, dv');
        lem_inv_latest_served_duty_is_rcvd_duty_dv_next(dv, e, dv');        
    }

    lemma lem_ind_inv_dv_next_invs_group_2(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_2(dv')
    {
        lem_inv_none_latest_served_duty_implies_none_current_proposer_duty_dv_next(dv, e, dv');
        lem_inv_current_proposer_duty_is_either_none_or_latest_served_duty_dv_next(dv, e, dv');
        lem_inv_available_current_proposer_duty_is_latest_served_proposer_duty_dv_next(dv, e, dv');        
    }

    lemma lem_ind_inv_dv_next_invs_group_3(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_3(dv')
    {
        lem_inv_no_duplicated_proposer_duties_dv_next(dv, e, dv');
        lem_inv_every_proposer_duty_before_dvn_proposer_index_was_delivered_dv_next(dv, e, dv');        
        lem_inv_no_active_consensus_instance_before_receiving_a_proposer_duty_dv_next(dv, e, dv');                        
    }

    lemma lem_ind_inv_dv_next_invs_group_4(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_4(dv')
    {
        lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_dv_next(dv, e, dv');                
        lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_dv_next(dv, e, dv');    
        lem_inv_consensus_instances_only_for_rcvd_duties_dv_next(dv, e, dv');    
        lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_dv_next(dv, e, dv');    
    }

    lemma lem_ind_inv_dv_next_invs_group_5(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_5(dv')
    {
        lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_dv_next(dv, e, dv');    
        lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_dv_next(dv, e, dv');  
        lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_dv_next(dv, e, dv');          
    }

    lemma lem_ind_inv_dv_next_invs_group_6(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_6(dv')
    {       
        lem_inv_every_db_in_block_slashing_db_hist_is_subset_of_block_slashing_db_dv_next(dv, e, dv');  
        lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_dv_next(dv, e, dv');  
    }

    lemma lem_ind_inv_dv_next_invs_group_7(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_7(dv')
    {               
        lem_inv_all_in_transit_messages_were_sent_dv_next(dv, e, dv');  
        lem_inv_rcvd_block_shares_are_from_sent_messages_dv_next(dv, e, dv');  
        lem_inv_slots_for_sent_validity_predicate_are_stored_in_block_slashing_db_hist(dv, e, dv');
    }

    lemma lem_ind_inv_implies_intermediate_steps_helper_1(dv: DVState)
    requires ind_inv(dv)
    ensures inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty(dv)
    ensures inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_proposer_duties(dv)
    {    
        lem_inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty_ind_inv(dv);
        lem_inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_proposer_duties_ind_inv(dv);
    }

    lemma lem_ind_inv_implies_intermediate_steps_helper_2(dv: DVState)
    requires ind_inv(dv)  
    ensures inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_proposer_duty_and_randao_reveal(dv)
    ensures inv_active_consensus_instances_implied_the_delivery_of_proposer_duties(dv)   
    ensures inv_same_node_status_in_dv_and_ci(dv)    
    ensures construct_complete_signed_block_assumptions_helper(
                dv.construct_complete_signed_block,
                dv.dv_pubkey,
                dv.all_nodes
            )  
    {    
        lem_inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_proposer_duty_and_randao_reveal_ind_inv(dv);
        lem_inv_active_consensus_instances_implied_the_delivery_of_proposer_duties_ind_inv(dv);
        lem_inv_same_node_status_in_dv_and_ci_ind_inv(dv);      
        lem_construct_complete_signed_block_assumptions_helper(dv);       
    }

    lemma lem_ind_inv_implies_intermediate_steps_helper_3(dv: DVState)
    requires ind_inv(dv)  
    ensures inv_seq_of_proposer_duties_is_ordered(dv)
    ensures inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist(dv)
    ensures inv_current_latest_proposer_duty_match(dv)
    ensures inv_rcvd_block_shares_are_in_all_sent_messages(dv)
    {            
        lem_inv_current_latest_proposer_duty_match(dv);
        lem_inv_rcvd_block_shares_are_from_sent_messages_inv_rcvd_block_shares_are_in_all_sent_messages(dv);
    }

    lemma lem_ind_inv_implies_intermediate_steps_helper_4(dv: DVState)
    requires ind_inv(dv)  
    ensures lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_new_precond(dv)    
    ensures inv_block_of_all_created_blocks_is_set_of_decided_values(dv)
    {   
        lem_ind_inv_implies_intermediate_steps_helper_1(dv);
        lem_ind_inv_implies_intermediate_steps_helper_2(dv);
        lem_ind_inv_implies_intermediate_steps_helper_3(dv);   
        lem_inv_block_of_all_created_blocks_is_set_of_decided_values_dv_next(dv);
    }

    lemma lem_ind_inv_implies_intermediate_steps(dv: DVState)
    requires ind_inv(dv)
    ensures inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty(dv)
    ensures inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_proposer_duties(dv)
    ensures inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_proposer_duty_and_randao_reveal(dv)
    ensures inv_active_consensus_instances_implied_the_delivery_of_proposer_duties(dv)   
    ensures inv_same_node_status_in_dv_and_ci(dv)    
    ensures construct_complete_signed_block_assumptions_helper(
                dv.construct_complete_signed_block,
                dv.dv_pubkey,
                dv.all_nodes
            )    
    ensures inv_seq_of_proposer_duties_is_ordered(dv)     
    ensures inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist(dv)
    ensures inv_current_latest_proposer_duty_match(dv)
    ensures inv_rcvd_block_shares_are_in_all_sent_messages(dv)
    ensures lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_new_precond(dv)
    ensures inv_block_of_all_created_blocks_is_set_of_decided_values(dv)
    {   
        lem_ind_inv_implies_intermediate_steps_helper_1(dv); 
        lem_ind_inv_implies_intermediate_steps_helper_2(dv);
        lem_ind_inv_implies_intermediate_steps_helper_3(dv);
        lem_ind_inv_implies_intermediate_steps_helper_4(dv);
        lem_inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_proposer_duty_and_randao_reveal_ind_inv(dv);
        lem_inv_block_of_all_created_blocks_is_set_of_decided_values_dv_next(dv);
    }
   
    // lemma lem_ind_inv_dv_next_inv_all_validity_predicates_are_stored_in_block_slashing_db_hist(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)  
    // requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    // requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')       
    // requires ind_inv(dv)
    // ensures inv_all_validity_predicates_are_stored_in_block_slashing_db_hist(dv')
    // {
    //     // lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_inv_active_block_consensus_instances_predicate_is_in_block_slashing_db_hist(dv);
    //     // assert inv_active_block_consensus_instances_predicate_is_in_block_slashing_db_hist(dv);

    //     // lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist(dv);
    //     // assert inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist(dv);

    //     // lem_ind_inv_implies_intermediate_steps(dv);
    //     // assert inv_same_node_status_in_dv_and_ci(dv);


    //     // assert && inv_all_validity_predicates_are_stored_in_block_slashing_db_hist(dv)
    //     //        && inv_quorum_constraints(dv)
    //     //        && inv_same_node_status_in_dv_and_ci(dv)
    //     //        && inv_only_dv_construct_complete_signing_functions(dv)    
    //     //        && inv_slots_for_sent_validity_predicate_are_stored_in_block_slashing_db_hist(dv)  
    //     //        && inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist(dv)
    //     //        && inv_active_block_consensus_instances_predicate_is_in_block_slashing_db_hist(dv)
    //     //        ;

    //     lem_inv_all_validity_predicates_are_stored_in_block_slashing_db_hist_dv_next(dv, e, dv');    
    //     assert inv_all_validity_predicates_are_stored_in_block_slashing_db_hist(dv');
    // }

    // lemma lem_ind_inv_dv_next_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    // requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    // requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    // requires ind_inv(dv)
    // ensures inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(dv')
    // {
    //     // lem_ind_inv_implies_intermediate_steps(dv);
    //     // assert construct_signed_block_signature_assumptions_helper(
    //     //         dv.construct_signed_block_signature,
    //     //         dv.dv_pubkey,
    //     //         dv.all_nodes);

    //     // lem_inv_all_in_transit_messages_were_sent_invNetwork(dv);
    //     // assert invNetwork(dv);

    //     // lem_inv_rcvd_block_shares_are_from_sent_messages_inv_rcvd_block_shares_are_in_all_sent_messages(dv);
    //     // assert inv_rcvd_block_shares_are_in_all_sent_messages(dv);

    //     // assert  && DV_Block_Proposer_Spec.NextEvent(dv, e, dv')
    //     //         && inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(dv)
    //     //         && construct_signed_block_signature_assumptions_helper(
    //     //             dv.construct_signed_block_signature,
    //     //             dv.dv_pubkey,
    //     //             dv.all_nodes
    //     //         )
    //     //         && inv_only_dv_construct_complete_signing_functions(dv)  
    //     //         && invNetwork(dv)
    //     //         && inv_quorum_constraints(dv)
    //     //         && inv_rcvd_block_shares_are_in_all_sent_messages(dv)
    //     //         ;

        
    //     lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_dv_next(dv, e, dv');
    //     assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(dv');
    // }

    // lemma lem_ind_inv_dv_next_inv_decided_value_of_consensus_instance_is_decided_by_quorum(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    // requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    // requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    // requires ind_inv(dv)
    // ensures inv_decided_value_of_consensus_instance_is_decided_by_quorum(dv')
    // {
    //     lem_inv_decided_value_of_consensus_instance_is_decided_by_quorum_dv_next(dv, e, dv');
    // }

    // lemma lem_ind_inv_dv_next_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    // requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    // requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    // requires ind_inv(dv)
    // ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(dv')
    // {
    //     lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv_dv_next(dv, e, dv');
    // }

    // lemma lem_ind_inv_dv_next_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    // requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    // requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    // requires ind_inv(dv)
    // ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(dv')
    // {
    //     lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(dv, e, dv');
    // }

    // lemma lem_ind_inv_dv_next_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    // requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    // requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    // requires ind_inv(dv)
    // ensures inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(dv')
    // {
    //     lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k_dv_next(dv, e, dv');
    // }

    
    lemma lem_ind_inv_dv_next_invs_group_8(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_8(dv')
    {
        lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_dv_next(dv, e, dv');
        lem_inv_decided_value_of_consensus_instance_is_decided_by_quorum_dv_next(dv, e, dv');  
        lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv_dv_next(dv, e, dv');
        lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_dv_next(dv, e, dv');
        // lem_ind_inv_dv_next_inv_all_validity_predicates_are_stored_in_block_slashing_db_hist(dv, e, dv');  
        // lem_ind_inv_dv_next_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(dv, e, dv');             
        // lem_ind_inv_dv_next_inv_decided_value_of_consensus_instance_is_decided_by_quorum(dv, e, dv');       
        // lem_ind_inv_dv_next_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(dv, e, dv');  
        // lem_ind_inv_dv_next_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(dv, e, dv');   
    }

    // lemma lem_ind_inv_dv_next_invNetwork(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    // requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    // requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    // requires ind_inv(dv)
    // ensures invNetwork(dv')
    // {
    //     lem_inv_all_in_transit_messages_were_sent_dv_next(dv, e, dv');
    //     lem_inv_all_in_transit_messages_were_sent_invNetwork(dv');
    // }

    // lemma lem_ind_inv_dv_next_inv_38(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    // requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    // requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    // requires ind_inv(dv)
    // ensures inv_block_shares_to_broadcast_are_sent_messages(dv')
    // {
    //     lem_ind_inv_implies_intermediate_steps(dv);
    //     assert inv_same_node_status_in_dv_and_ci(dv);
    //     lem_inv_block_shares_to_broadcast_are_sent_messages_dv_next(dv, e, dv');
    // }

    // lemma lem_ind_inv_dv_next_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    // requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    // requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    // requires ind_inv(dv)
    // ensures inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist(dv')
    // {
    //     lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist(dv, e, dv');
    // }

    lemma lem_ind_inv_dv_next_invs_group_9(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_9(dv')
    {
        lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k_dv_next(dv, e, dv');
        lem_inv_all_in_transit_messages_were_sent_dv_next(dv, e, dv');
        lem_inv_all_in_transit_messages_were_sent_invNetwork(dv');
        lem_inv_block_shares_to_broadcast_are_sent_messages_dv_next(dv, e, dv');        
    }

    lemma lem_ind_inv_dv_next_invs_group_10(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_10(dv')
    {        
        lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_dv_next(dv, e, dv');
        lem_ind_inv_implies_intermediate_steps(dv);        
        lem_inv_available_current_proposer_duty_is_from_dv_seq_of_proposer_duties_dv_next(dv, e, dv');        
        lem_inv_block_of_in_transit_block_share_is_decided_value_dv_next(dv, e, dv');
        lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_dv_next(dv, e, dv');
    }
    
    // lemma lem_ind_inv_dv_next_inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    // requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    // requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    // requires ind_inv(dv)
    // ensures inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv(dv')
    // {
    //     lem_ind_inv_implies_intermediate_steps_helper_4(dv);
    //     assert lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_new_precond(dv);
    //     lem_inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv(dv, e, dv');
    // }

    // lemma lem_ind_inv_dv_next_inv_slot_in_future_beacon_block_is_correct(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    // requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    // requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    // requires ind_inv(dv)
    // ensures inv_slot_in_future_beacon_block_is_correct(dv')
    // {
    //     lem_ind_inv_implies_intermediate_steps_helper_4(dv);
    //     lem_inv_slot_in_future_beacon_block_is_correct_dv_next(dv, e, dv');
    // }

    lemma lem_ind_inv_dv_next_invs_group_11(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_11(dv')
    {
        lem_ind_inv_implies_intermediate_steps_helper_4(dv);
        lem_inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv(dv, e, dv');
        lem_inv_slot_in_future_beacon_block_is_correct_dv_next(dv, e, dv');    
        lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_dv_next(dv, e, dv');   
        lem_inv_unique_rcvd_proposer_duty_per_slot_dv_next(dv, e, dv');     
    }

    lemma lem_ind_inv_dv_next_invs_group_12(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_12(dv')
    {
        lem_ind_inv_implies_intermediate_steps_helper_4(dv);
        lem_inv_consensus_instance_isConditionForSafetyTrue_dv_next(dv, e, dv');   
        lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_dv_next(dv, e, dv');  
        lem_inv_sent_validity_predicate_only_for_slots_stored_in_block_slashing_db_hist(dv, e, dv');
        lem_inv_all_validity_predicates_are_stored_in_block_slashing_db_hist_dv_next(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_invs_group_13(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_13(dv')
    {
        lem_inv_unchanged_dvc_rs_pubkey_dv_next(dv, e, dv');
        lem_inv_all_created_signed_beacon_blocks_are_valid_dv_next(dv, e, dv');
        lem_inv_complete_block_is_created_with_shares_from_quorum_dv_next(dv, e, dv');
        lem_inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block_dv_next(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_invs_group_14(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_14(dv')
    {   
        lem_inv_seq_of_proposer_duties_is_ordered_dv_next(dv, e, dv');
        lem_inv_block_shares_to_broadcast_is_tracked_in_block_slashing_db_dv_next(dv, e, dv');
        lem_inv_block_of_block_shares_is_known_dv_next(dv, e, dv');
        lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_proposer_duty_dv_next(dv, e, dv');
        lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_for_lower_slots_dv_next(dv, e, dv');        
    }

    lemma lem_ind_inv_dv_next_invs_group_15(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_15(dv')
    {   
        lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_dv_next(dv, e, dv');
        lem_inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_dv_next(dv, e, dv');
        
        lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_dv_next(dv, e, dv');
        lem_inv_block_of_in_transit_block_share_is_decided_value_dv_next(dv, e, dv');
        lem_inv_all_created_signed_beacon_blocks_are_valid_dv_next(dv, e, dv');
        lem_inv_block_of_all_created_blocks_is_set_of_decided_values_dv_next(dv');
        lem_inv_at_most_submitted_signed_beacon_block_for_every_slot_dv_next(dv');
    }
    
    lemma lem_ind_inv_dv_next_ind_inv_helper_1(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_1(dv')
    ensures invs_group_2(dv')
    ensures invs_group_3(dv')
    {
        lem_ind_inv_dv_next_invs_group_1(dv, e, dv');
        lem_ind_inv_dv_next_invs_group_2(dv, e, dv');
        lem_ind_inv_dv_next_invs_group_3(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_ind_inv_helper_2(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)  
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv)    
    ensures invs_group_4(dv')
    ensures invs_group_5(dv')
    ensures invs_group_6(dv')
    ensures invs_group_7(dv') 
    ensures invs_group_8(dv')
    {
        lem_ind_inv_dv_next_invs_group_4(dv, e, dv');
        lem_ind_inv_dv_next_invs_group_5(dv, e, dv');
        lem_ind_inv_dv_next_invs_group_6(dv, e, dv');
        lem_ind_inv_dv_next_invs_group_7(dv, e, dv');
        lem_ind_inv_dv_next_invs_group_8(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_ind_inv_helper_3(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_9(dv')
    ensures invs_group_10(dv')
    ensures invs_group_11(dv')
    {        
        lem_ind_inv_dv_next_invs_group_9(dv, e, dv');       
        lem_ind_inv_dv_next_invs_group_10(dv, e, dv');  
        lem_ind_inv_dv_next_invs_group_11(dv, e, dv');                                     
    }

    lemma lem_ind_inv_dv_next_ind_inv_helper_4(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_12(dv')   
    ensures invs_group_13(dv')            
    {        
        lem_ind_inv_dv_next_invs_group_12(dv, e, dv');                              
        lem_ind_inv_dv_next_invs_group_13(dv, e, dv');             
    }

    lemma lem_ind_inv_dv_next_ind_inv_helper_5(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv)    
    ensures invs_group_14(dv')
    ensures invs_group_15(dv')
    {        
        lem_ind_inv_dv_next_invs_group_14(dv, e, dv');                              
        lem_ind_inv_dv_next_invs_group_15(dv, e, dv');                              
    }

    lemma lem_ind_inv_dv_next_ind_inv_helper_a(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv) 
    ensures invs_group_1(dv')
    ensures invs_group_2(dv')
    ensures invs_group_3(dv')
    ensures invs_group_4(dv')
    ensures invs_group_5(dv')
    ensures invs_group_6(dv')
    ensures invs_group_7(dv')
    ensures invs_group_8(dv')    
    {
        lem_ind_inv_dv_next_ind_inv_helper_1(dv, e, dv');                          
        lem_ind_inv_dv_next_ind_inv_helper_2(dv, e, dv');    
    }

    lemma lem_ind_inv_dv_next_ind_inv_helper_b(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv) 
    ensures invs_group_9(dv')    
    ensures invs_group_10(dv')    
    ensures invs_group_11(dv')    
    ensures invs_group_12(dv')    
    ensures invs_group_13(dv')    
    ensures invs_group_14(dv')
    ensures invs_group_15(dv')
    {
        lem_ind_inv_dv_next_ind_inv_helper_3(dv, e, dv');   
        lem_ind_inv_dv_next_ind_inv_helper_4(dv, e, dv');    
        lem_ind_inv_dv_next_ind_inv_helper_5(dv, e, dv');    
    }

    lemma lem_ind_inv_dv_next_ind_inv_helper(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv) 
    ensures invs_group_1(dv')
    ensures invs_group_2(dv')   
    ensures invs_group_3(dv')   
    ensures invs_group_4(dv')   
    ensures invs_group_5(dv')   
    ensures invs_group_6(dv')
    ensures invs_group_7(dv')
    ensures invs_group_8(dv')
    ensures invs_group_9(dv')    
    ensures invs_group_10(dv')    
    ensures invs_group_11(dv')    
    ensures invs_group_12(dv')    
    ensures invs_group_13(dv')    
    ensures invs_group_14(dv')    
    ensures invs_group_15(dv')    
    {   
        lem_ind_inv_dv_next_ind_inv_helper_a(dv, e, dv');
        lem_ind_inv_dv_next_ind_inv_helper_b(dv, e, dv');                
    }

    lemma lem_ind_inv_dv_next_ind_inv(dv: DVState, e: DV_Block_Proposer_Spec.Event, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextEventPreCond(dv, e)
    requires DV_Block_Proposer_Spec.NextEvent(dv, e, dv')  
    requires ind_inv(dv)    
    ensures ind_inv(dv')    
    {   
        lem_ind_inv_dv_next_ind_inv_helper(dv, e, dv');                                  
    }

    lemma lem_ind_inv_dv_ind_inv_NextPreCond(dv: DVState, dv': DVState)       
    requires DV_Block_Proposer_Spec.NextPreCond(dv)
    requires DV_Block_Proposer_Spec.Next(dv, dv')  
    requires ind_inv(dv)    
    ensures ind_inv(dv')  
    ensures DV_Block_Proposer_Spec.NextPreCond(dv')
    {
        var e :|
            && validEvent(dv, e)
            && NextEvent(dv, e, dv');

        lem_ind_inv_dv_next_ind_inv(dv, e, dv');
        lem_NextPreCond(dv');
    } 

    lemma lem_NextPreCond(
        s: DVState
    )
    requires ind_inv(s)
    ensures  NextPreCond(s)                
    {
        forall event | validEvent(s, event)
        ensures NextEventPreCond(s, event);
        {
            if event.HonestNodeTakingStep?
            {

            }
        }

    }     
}