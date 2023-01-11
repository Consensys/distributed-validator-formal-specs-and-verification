include "../../../../common/commons.dfy"
include "../../common/attestation_creation_instrumented.dfy"
include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_attestation_creation.dfy"
include "../../../../specs/dvc/dvc_attestation_creation.dfy"

include "../../../common/helper_sets_lemmas.dfy"
include "../../../no_slashable_attestations/common/common_proofs.dfy"
include "../../../no_slashable_attestations/common/dvc_spec_axioms.dfy"

include "invs_fnc_1.dfy"
include "invs_fnc_2.dfy"
include "invs_dv_next_1.dfy"
include "invs_dv_next_2.dfy"
include "invs_dv_next_3.dfy"
include "invs_dv_next_4.dfy"
include "invs_dv_next_5.dfy"
include "invs_dv_next_6.dfy"

include "../inv.dfy"
include "../ind_inv.dfy"

include "proofs_intermediate_steps.dfy"

module Ind_Inv_DV_Next
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Spec
    import opened DV
    import opened Att_Ind_Inv_With_Empty_Init_Att_Slashing_DB
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Invs_DV_Next_3
    import opened Invs_DV_Next_4
    import opened Fnc_Invs_1
    import opened Helper_Sets_Lemmas
    import opened Invs_DV_Next_1
    import opened Proofs_Intermediate_Steps
    import opened Invs_DV_Next_2
    import opened Invs_DV_Next_5
    import opened Invs_DV_Next_6

    lemma lem_ind_inv_dv_next_invs_group_1(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_1(dv')
    {    
        lem_inv_quorum_constraints_dv_next(dv, e, dv');
        lem_inv_unchanged_honesty_dv_next(dv, e, dv');
        lem_inv_only_dv_construct_signed_attestation_signature_dv_next(dv, e, dv');
        lem_inv_queued_att_duty_is_dvn_seq_of_att_duty_dv_next(dv, e, dv');
        lem_inv_queued_att_duty_is_rcvd_duty_dv_next(dv, e, dv');
        lem_inv_current_att_duty_is_rcvd_duty_dv_next(dv, e, dv');
        lem_inv_latest_served_duty_is_rcvd_duty_dv_next(dv, e, dv');        
    }

    lemma lem_ind_inv_dv_next_invs_group_2(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_2(dv')
    {
        lem_inv_none_latest_served_duty_implies_none_current_att_duty_dv_next(dv, e, dv');
        lem_inv_current_att_duty_is_either_none_or_latest_served_duty_dv_next(dv, e, dv');
        lem_inv_available_current_att_duty_is_latest_served_att_duty_dv_next(dv, e, dv');        
        lem_inv_is_sequence_attestation_duties_to_be_serves_orders_dv_next(dv, e, dv');                
    }

    lemma lem_ind_inv_dv_next_invs_group_3(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_3(dv')
    {
        lem_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_dv_next(dv, e, dv');
        lem_inv_strictly_increasing_queue_of_att_duties_dv_next(dv, e, dv');
        lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_dv_next(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_invs_group_4(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_4(dv')
    {
        lem_inv_no_duplicated_att_duties_dv_next(dv, e, dv');
        lem_inv_every_att_duty_before_dvn_att_index_was_delivered_dv_next(dv, e, dv');        
        lem_inv_no_active_consensus_instance_before_receiving_an_att_duty_dv_next(dv, e, dv');                        
    }

    lemma lem_ind_inv_dv_next_invs_group_5(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_5(dv')
    {
        lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_dv_next(dv, e, dv');                
        lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_dv_next(dv, e, dv');    
        lem_inv_consensus_instances_only_for_rcvd_duties_dv_next(dv, e, dv');    
    }


    lemma lem_ind_inv_dv_next_invs_group_6(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_6(dv')
    {
        lem_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_dv_next(dv, e, dv');    
        lem_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_dv_next(dv, e, dv');  
        lem_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_dv_next(dv, e, dv');          
    }

    lemma lem_ind_inv_dv_next_invs_group_7(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_7(dv')
    {       
        lem_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_dv_next(dv, e, dv');  
        lem_inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_dv_next(dv, e, dv');  
        lem_inv_construct_signed_attestation_signature_assumptions_helper_dv_next(dv, e, dv');  
        // lem_inv_all_in_transit_messages_were_sent_dv_next(dv, e, dv');  
        // lem_inv_rcvd_attn_shares_are_from_sent_messages_dv_next(dv, e, dv');  
        // Invs_DV_Next_5.lem_inv_33(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_invs_group_8(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_8(dv')
    {               
        lem_inv_all_in_transit_messages_were_sent_dv_next(dv, e, dv');  
        lem_inv_rcvd_attn_shares_are_from_sent_messages_dv_next(dv, e, dv');  
        Invs_DV_Next_5.lem_inv_33(dv, e, dv');
    }


    lemma lem_ind_inv_implies_intermediate_steps_helper_1(dv: DVState)
    requires ind_inv(dv)
    ensures concl_next_att_duty_is_higher_than_current_att_duty(dv)
    ensures concl_next_att_duty_is_higher_than_latest_served_att_duty(dv)
    ensures concl_future_att_duty_is_higher_than_rcvd_att_duty(dv)
    ensures concl_future_att_duty_is_higher_than_queued_att_duty(dv)
    ensures concl_slot_of_active_consensus_instance_is_lower_than_slot_of_queued_att_duty(dv)    
    {    
        lem_concl_next_att_duty_is_higher_than_current_att_duty_ind_inv(dv);
        lem_concl_next_att_duty_is_higher_than_latest_served_att_duty_ind_inv(dv);
        lem_concl_future_att_duty_is_higher_than_rcvd_att_duty_ind_inv(dv);
        lem_concl_future_att_duty_is_higher_than_queued_att_duty_ind_inv(dv);
        lem_concl_slot_of_active_consensus_instance_is_lower_than_slot_of_queued_att_duty_ind_inv(dv);  
    }

    lemma lem_ind_inv_implies_intermediate_steps_helper_2(dv: DVState)
    requires ind_inv(dv)  
    ensures inv_queued_att_duty_is_rcvd_duty0(dv)
    ensures inv_queued_att_duty_is_rcvd_duty1(dv)   
    ensures same_honest_nodes_in_dv_and_ci(dv)    
    ensures construct_signed_attestation_signature_assumptions_helper(
                dv.construct_signed_attestation_signature,
                dv.dv_pubkey,
                dv.all_nodes)  
    {    
        lem_inv_queued_att_duty_is_rcvd_duty0_ind_inv(dv);
        lem_inv_queued_att_duty_is_rcvd_duty1_ind_inv(dv);
        lem_inv_queued_att_duty_is_rcvd_duty3_ind_inv(dv);      
        lem_construct_signed_attestation_signature_assumptions_helper(dv);       
    }

    lemma lem_ind_inv_implies_intermediate_steps_helper_3(dv: DVState)
    requires ind_inv(dv)  
    ensures inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(dv)  
    ensures is_sequence_attestation_duties_to_be_served_orderd(dv)
    ensures inv_attestation_duty_queue_is_ordered(dv)
    ensures inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(dv)
    ensures pred_inv_current_latest_attestation_duty_match(dv)
    ensures pred_rcvd_attestation_shares_is_in_all_messages_sent(dv)
    {    
        lem_inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(dv);
        lem_inv_attestation_duty_queue_is_ordered(dv);
        lem_inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(dv);
        lem_pred_inv_current_latest_attestation_duty_match(dv);
        lem_inv_rcvd_attn_shares_are_from_sent_messages_pred_rcvd_attestation_shares_is_in_all_messages_sent(dv);
    }

    lemma lem_ind_inv_implies_intermediate_steps_helper_4(dv: DVState)
    requires ind_inv(dv)  
    ensures lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_precond(dv)
    ensures lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(dv)    
    {   
        lem_ind_inv_implies_intermediate_steps_helper_1(dv);
        lem_ind_inv_implies_intermediate_steps_helper_2(dv);
        lem_ind_inv_implies_intermediate_steps_helper_3(dv);        
    }

    lemma lem_ind_inv_implies_intermediate_steps(dv: DVState)
    requires ind_inv(dv)
    ensures concl_next_att_duty_is_higher_than_current_att_duty(dv)
    ensures concl_next_att_duty_is_higher_than_latest_served_att_duty(dv)
    ensures concl_future_att_duty_is_higher_than_rcvd_att_duty(dv)
    ensures concl_future_att_duty_is_higher_than_queued_att_duty(dv)
    ensures concl_slot_of_active_consensus_instance_is_lower_than_slot_of_queued_att_duty(dv)    
    ensures inv_queued_att_duty_is_rcvd_duty0(dv)
    ensures inv_queued_att_duty_is_rcvd_duty1(dv)   
    ensures same_honest_nodes_in_dv_and_ci(dv)    
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
    ensures lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_precond(dv)
    ensures lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(dv)
    {   
        lem_ind_inv_implies_intermediate_steps_helper_1(dv); 
        lem_ind_inv_implies_intermediate_steps_helper_2(dv);
        lem_ind_inv_implies_intermediate_steps_helper_3(dv);
        lem_ind_inv_implies_intermediate_steps_helper_4(dv);
    }
   
    lemma lem_ind_inv_dv_next_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv: DVState, e: DV.Event, dv': DVState)  
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')       
    requires ind_inv(dv)
    ensures inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv')
    {
        lem_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_inv_active_attestation_consensus_instances_predicate_is_in_att_slashing_db_hist(dv);
        assert inv_active_attestation_consensus_instances_predicate_is_in_att_slashing_db_hist(dv);

        lem_inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(dv);
        assert inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(dv);

        lem_ind_inv_implies_intermediate_steps(dv);
        assert same_honest_nodes_in_dv_and_ci(dv);


        assert && inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv)
               && inv_quorum_constraints(dv)
               && same_honest_nodes_in_dv_and_ci(dv)
               && inv_only_dv_construct_signed_attestation_signature(dv)    
               && inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper(dv)  
               && inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(dv)
               && inv_active_attestation_consensus_instances_predicate_is_in_att_slashing_db_hist(dv)
               ;

        lem_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv, e, dv');    
        assert inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv');
    }

    lemma lem_ind_inv_dv_next_inv_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv')
    {
        lem_ind_inv_implies_intermediate_steps(dv);
        assert construct_signed_attestation_signature_assumptions_helper(
                dv.construct_signed_attestation_signature,
                dv.dv_pubkey,
                dv.all_nodes);

        lem_inv_all_in_transit_messages_were_sent_invNetwork(dv);
        assert invNetwork(dv);

        lem_inv_rcvd_attn_shares_are_from_sent_messages_pred_rcvd_attestation_shares_is_in_all_messages_sent(dv);
        assert pred_rcvd_attestation_shares_is_in_all_messages_sent(dv);

        assert  && DV.NextEvent(dv, e, dv')
                && concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv)
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

        
        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv, e, dv');
        assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv');
    }

    lemma lem_ind_inv_dv_next_inv_decided_value_of_consensus_instance_is_decided_by_quorum(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_decided_value_of_consensus_instance_is_decided_by_quorum(dv')
    {
        lem_inv_decided_value_of_consensus_instance_is_decided_by_quorum(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(dv')
    {
        lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(dv')
    {
        lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(dv')
    {
        lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(dv, e, dv');
    }

    
    lemma lem_ind_inv_dv_next_invs_group_9(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_9(dv')
    {
        lem_ind_inv_dv_next_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv, e, dv');  
        lem_ind_inv_dv_next_inv_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv, e, dv');             
        lem_ind_inv_dv_next_inv_decided_value_of_consensus_instance_is_decided_by_quorum(dv, e, dv');       
        lem_ind_inv_dv_next_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(dv, e, dv');  
        lem_ind_inv_dv_next_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(dv, e, dv');   
    }

    lemma lem_ind_inv_dv_next_invNetwork(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invNetwork(dv')
    {
        lem_inv_all_in_transit_messages_were_sent_dv_next(dv, e, dv');
        lem_inv_all_in_transit_messages_were_sent_invNetwork(dv');
    }

    lemma lem_ind_inv_dv_next_inv_38(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_attestation_shares_to_broadcast_are_sent_messages(dv')
    {
        lem_ind_inv_implies_intermediate_steps(dv);
        assert same_honest_nodes_in_dv_and_ci(dv);
        lem_inv_attestation_shares_to_broadcast_are_sent_messages_dv_next(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist(dv')
    {
        lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_invs_group_10(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_10(dv')
    {
        lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(dv, e, dv');
        lem_ind_inv_dv_next_invNetwork(dv, e, dv');
        lem_ind_inv_dv_next_inv_38(dv, e, dv');
        lem_inv_attestation_shares_to_broadcast_are_sent_messages_inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(dv');
    }

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_ind_inv(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )
    requires NextEvent.requires(dv, event, dv')
    requires NextEvent(dv, event, dv')
    requires ind_inv(dv)
    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values(dv')
    {
        lem_ind_inv_implies_intermediate_steps_helper_4(dv);
        assert lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_precond(dv);
        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values(dv, event, dv');
    }

    lemma lem_ind_inv_dv_next_invs_group_11(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_11(dv')
    {        
        lem_ind_inv_dv_next_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist(dv, e, dv');
        lem_inv_available_latest_attestation_duty_is_from_dv_seq_of_att_duties_new_body_dv_next(dv, e, dv');
        lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a(dv, e, dv');
        lem_ind_inv_implies_intermediate_steps(dv);
        lem_pred_data_of_att_share_is_decided_value(dv, e, dv');
    }
    
    lemma lem_ind_inv_dv_next_invs_group_12(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_12(dv')
    {        
        lem_inv_attestation_duty_queue_is_ordered_3(dv, e, dv');
        lem_inv_attestation_duty_queue_is_ordered_4(dv, e, dv');        
    }

    lemma lem_ind_inv_dv_next_inv_queued_att_duties_are_from_dv_seq_of_att_duties(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_queued_att_duties_are_from_dv_seq_of_att_duties(dv')
    {
        lem_ind_inv_implies_intermediate_steps_helper_4(dv);
        lem_inv_queued_att_duties_are_from_dv_seq_of_att_duties_dv_next(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_inv_inv_decided_values_of_previous_duties_are_known_new(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_decided_values_of_previous_duties_are_known_new(dv')
    {
        lem_ind_inv_implies_intermediate_steps_helper_4(dv);
        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_inv_g_d_a(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_g_d_a(dv')
    {
        lem_ind_inv_implies_intermediate_steps_helper_4(dv);
        lem_inv_g_d_a(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_inv_g_d_b(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_g_d_b(dv')
    {
        lem_ind_inv_implies_intermediate_steps_helper_4(dv);
        lem_inv_g_d_b(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_inv_exists_decided_value_for_every_duty_before_queued_duties(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_exists_decided_value_for_every_duty_before_queued_duties(dv')
    {
        lem_ind_inv_implies_intermediate_steps_helper_4(dv);
        lem_inv_exists_decided_value_for_every_duty_before_queued_duties(dv, e, dv');
    }



    lemma lem_ind_inv_dv_next_invs_group_13(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_13(dv')
    {
        lem_ind_inv_implies_intermediate_steps_helper_4(dv);
        
        lem_inv_queued_att_duties_are_from_dv_seq_of_att_duties_dv_next(dv, e, dv');
        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new(dv, e, dv');
        lem_inv_g_d_a(dv, e, dv');
        lem_inv_g_d_b(dv, e, dv');        
        lem_inv_exists_decided_value_for_every_duty_before_queued_duties(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_invs_group_14(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_14(dv')
    {
        lem_ind_inv_implies_intermediate_steps_helper_4(dv);

        lem_inv_g_a_iii(dv, e, dv');
        lem_inv_g_a_iv_a(dv, e, dv');
        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values(dv, e, dv');        
    }

    lemma lem_ind_inv_dv_next_invs_group_15(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_15(dv')
    {
        lem_ind_inv_implies_intermediate_steps_helper_4(dv);

        lem_inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv, e, dv');
        lem_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv, e, dv');
        lem_inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_next_honest(dv, e, dv');       
    }
    
    lemma lem_ind_inv_dv_next_ind_inv_helper_1(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_1(dv')
    ensures invs_group_2(dv')
    ensures invs_group_3(dv')
    {
        lem_ind_inv_dv_next_invs_group_1(dv, e, dv');
        lem_ind_inv_dv_next_invs_group_2(dv, e, dv');
        lem_ind_inv_dv_next_invs_group_3(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_ind_inv_helper_2(dv: DVState, e: DV.Event, dv': DVState)  
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
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

    lemma lem_ind_inv_dv_next_ind_inv_helper_3(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_9(dv')
    ensures invs_group_10(dv')
    ensures invs_group_11(dv')
    ensures invs_group_12(dv')    
    {        
        lem_ind_inv_dv_next_invs_group_9(dv, e, dv');       
        lem_ind_inv_dv_next_invs_group_10(dv, e, dv');  
        lem_ind_inv_dv_next_invs_group_11(dv, e, dv');            
        lem_ind_inv_dv_next_invs_group_12(dv, e, dv');                              
    }

    lemma lem_ind_inv_dv_next_ind_inv_helper_4(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)    
    ensures invs_group_13(dv')
    ensures invs_group_14(dv')
    ensures invs_group_15(dv')
    {                 
        lem_ind_inv_dv_next_invs_group_13(dv, e, dv');            
        lem_ind_inv_dv_next_invs_group_14(dv, e, dv');            
        lem_ind_inv_dv_next_invs_group_15(dv, e, dv');            
    }

    lemma lem_ind_inv_dv_next_ind_inv_helper_a(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
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

    lemma lem_ind_inv_dv_next_ind_inv_helper_b(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
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
    }

    lemma lem_ind_inv_dv_next_ind_inv_helper(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
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

    lemma lem_ind_inv_dv_next_ind_inv(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)    
    ensures ind_inv(dv')    
    {   
        lem_ind_inv_dv_next_ind_inv_helper(dv, e, dv');                                  
    }

    lemma lem_ind_inv_dv_ind(dv: DVState, dv': DVState)       
    requires DV.NextPreCond(dv)
    requires DV.Next(dv, dv')  
    requires ind_inv(dv)    
    ensures ind_inv(dv')  
    ensures DV.NextPreCond(dv')
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
    requires inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue(s);
    requires is_sequence_attestation_duties_to_be_served_orderd(s)
    requires inv_queued_att_duties_are_from_dv_seq_of_att_duties(s)
    requires inv_latest_attestation_duty_is_from_dv_seq_of_att_duties(s)
    requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty(s)
    requires inv_no_active_consensus_instance_before_receiving_an_att_duty(s)
    requires inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(s)   
    ensures  NextPreCond(s)                
    {
        forall event | validEvent(s, event)
        ensures NextEventPreCond(s, event);
        {
            if event.HonestNodeTakingStep?
            {
                lem_NextEventPreCond(s, event);
            }
        }

    }       
}