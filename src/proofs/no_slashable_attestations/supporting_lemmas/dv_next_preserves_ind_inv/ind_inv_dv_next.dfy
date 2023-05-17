include "../../../../common/commons.dfy"
include "../../common/dvc_attestation_creation_instrumented.dfy"
include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_attestation_creation.dfy"
include "../../../../specs/dvc/dvc_attestation_creation.dfy"

include "../../../no_slashable_attestations/common/common_proofs.dfy"
include "../../../bn_axioms.dfy"
include "../../../rs_axioms.dfy"


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

module Ind_Inv_Att_DV_Next
{
    import opened Types 
    import opened Common_Functions
    import opened Set_Seq_Helper
    import opened Signing_Methods
    import opened Consensus
    import opened Consensus_Engine
    import opened Network_Spec
    import opened Att_DVC
    import opened Att_DV
    import opened Att_DV_Assumptions
    import opened Att_Ind_Inv_With_Empty_Init_Att_Slashing_DB
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Invs_Att_DV_Next_1
    import opened Invs_Att_DV_Next_2
    import opened Invs_Att_DV_Next_3
    import opened Invs_Att_DV_Next_4
    import opened Invs_Att_DV_Next_5
    import opened Proofs_Intermediate_Steps
    

    lemma lem_ind_inv_dv_next_invs_group_1(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_1(dv')
    {    
        lem_inv_all_honest_nodes_is_quorum_dv_next(dv, e, dv');
        lem_inv_unchanged_paras_of_consensus_instances_dv_next(dv, e, dv');
        lem_inv_only_dv_construct_signed_attestation_signature_dv_next(dv, e, dv');
        lem_inv_current_att_duty_is_rcvd_duty_dv_next(dv, e, dv');
        lem_inv_latest_att_duty_is_rcvd_duty_dv_next(dv, e, dv');        
    }

    lemma lem_ind_inv_dv_next_invs_group_2(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_2(dv')
    {
        lem_inv_none_latest_att_duty_implies_none_current_att_duty_dv_next(dv, e, dv');
        lem_inv_current_att_duty_is_either_none_or_latest_att_duty_dv_next(dv, e, dv');
        lem_inv_available_current_att_duty_is_latest_att_duty_dv_next(dv, e, dv');        
        lem_assump_seq_of_att_duties_is_in_order_of_slots_dv_next(dv, e, dv');                
    }

    lemma lem_ind_inv_dv_next_invs_group_3(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_3(dv')
    {
        lem_inv_no_duplicated_att_duties_dv_next(dv, e, dv');
        lem_inv_every_att_duty_before_dv_att_index_was_delivered_dv_next(dv, e, dv');        
        lem_inv_no_active_consensus_instances_before_first_att_duty_was_received_dv_next(dv, e, dv');                        
    }

    lemma lem_ind_inv_dv_next_invs_group_4(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_4(dv')
    {
        lem_inv_att_duty_in_next_delivery_is_not_lower_than_rcvd_att_duties_ind_inv(dv);
        lem_inv_slots_of_active_consensus_instances_are_not_higher_than_slot_of_latest_att_duty_dv_next(dv, e, dv');                
        lem_inv_dvc_has_corresponding_att_duty_for_every_active_attestation_consensus_instance_dv_next(dv, e, dv');    
        lem_inv_consensus_instance_indexed_k_is_for_rcvd_duty_at_slot_k_dv_next(dv, e, dv');    
        lem_inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_dv_next(dv, e, dv');    
    }

    lemma lem_ind_inv_dv_next_invs_group_5(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_5(dv')
    {
        lem_inv_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_dv_next(dv, e, dv');    
        lem_inv_exist_db_in_slashing_db_hist_and_att_duty_for_every_validity_predicate_dv_next(dv, e, dv');  
        lem_inv_current_validity_predicate_for_slot_k_is_stored_in_slashing_db_hist_k_dv_next(dv, e, dv');          
    }

    lemma lem_ind_inv_dv_next_invs_group_6(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_6(dv')
    {       
        lem_inv_every_db_in_slashing_db_hist_is_subset_of_att_slashing_db_dv_next(dv, e, dv');  
        lem_inv_active_att_consensus_instances_are_tracked_in_slashing_db_hist_dv_next(dv, e, dv');  
        lem_inv_only_dv_construct_signed_attestation_signatures_dv_next(dv, e, dv');  
    }

    lemma lem_ind_inv_dv_next_invs_group_7(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_7(dv')
    {               
        lem_inv_all_in_transit_messages_were_sent_dv_next(dv, e, dv');  
        lem_inv_rcvd_att_shares_are_from_sent_messages_dv_next(dv, e, dv');  
        Invs_Att_DV_Next_5.lem_inv_slots_for_sent_validity_predicates_are_stored_in_slashing_db_hist_dv_next(dv, e, dv');
    }

    lemma lem_ind_inv_implies_intermediate_steps_helper_1(dv: AttDVState)
    requires ind_inv(dv)
    ensures inv_att_duty_in_next_delivery_is_not_lower_than_current_att_duty(dv)
    ensures inv_att_duty_in_next_delivery_is_not_lower_than_latest_att_duty(dv)
    ensures inv_att_duty_in_next_delivery_is_not_lower_than_rcvd_att_duties(dv)
    {    
        lem_inv_att_duty_in_next_delivery_is_not_lower_than_current_att_duty_ind_inv(dv);
        lem_inv_att_duty_in_next_delivery_is_not_lower_than_latest_att_duty_ind_inv(dv);
        lem_inv_att_duty_in_next_delivery_is_not_lower_than_rcvd_att_duties_ind_inv(dv);
    }

    lemma lem_ind_inv_implies_intermediate_steps_helper_2(dv: AttDVState)
    requires ind_inv(dv)  
    ensures inv_every_sent_validity_predicate_is_based_on_existing_slashing_db_and_rcvd_att_duty(dv)
    ensures inv_active_consensus_instances_imply_delivery_of_att_duties(dv)   
    ensures same_honest_nodes_in_dv_and_ci(dv)    
    ensures assump_construction_of_signed_attestation_signatures(
                dv.construct_signed_attestation_signature,
                dv.dv_pubkey,
                dv.all_nodes)  
    {    
        lem_inv_every_sent_validity_predicate_is_based_on_existing_slashing_db_and_rcvd_att_duty_ind_inv(dv);
        lem_inv_active_consensus_instances_imply_delivery_of_att_duties_ind_inv(dv);
        lem_inv_queued_att_duty_is_rcvd_duty3_ind_inv(dv);      
        lem_assump_construction_of_signed_attestation_signatures(dv);       
    }

    lemma lem_ind_inv_implies_intermediate_steps_helper_3(dv: AttDVState)
    requires ind_inv(dv)  
    ensures assump_seq_of_att_duties_is_in_order_of_slots(dv.sequence_of_attestation_duties_to_be_served)
    ensures inv_domain_of_active_consensus_instances_is_subset_of_slashing_db_hist(dv)
    ensures inv_available_current_att_duty_is_latest_att_duty(dv)
    ensures inv_rcvd_attestation_shares_are_sent_messages(dv)
    {    
        lem_inv_domain_of_active_consensus_instances_is_subset_of_slashing_db_hist(dv);
        lem_inv_available_current_att_duty_is_latest_att_duty(dv);
        lem_inv_rcvd_att_shares_are_from_sent_messages_inv_rcvd_attestation_shares_are_sent_messages(dv);
    }

    lemma lem_ind_inv_implies_intermediate_steps_helper_4(dv: AttDVState)
    requires ind_inv(dv)  
    ensures lem_inv_exists_honest_node_that_sent_att_share_for_every_submitted_att_new_precond(dv)    
    ensures inv_data_of_all_created_attestations_is_set_of_decided_values(dv)
    {   
        lem_ind_inv_implies_intermediate_steps_helper_1(dv);
        lem_ind_inv_implies_intermediate_steps_helper_2(dv);
        lem_ind_inv_implies_intermediate_steps_helper_3(dv);   
        lem_inv_data_of_all_created_attestations_is_set_of_decided_values_dv_next(dv);
    }

    lemma lem_ind_inv_implies_intermediate_steps(dv: AttDVState)
    requires ind_inv(dv)
    ensures inv_att_duty_in_next_delivery_is_not_lower_than_current_att_duty(dv)
    ensures inv_att_duty_in_next_delivery_is_not_lower_than_latest_att_duty(dv)
    ensures inv_att_duty_in_next_delivery_is_not_lower_than_rcvd_att_duties(dv)
    ensures inv_every_sent_validity_predicate_is_based_on_existing_slashing_db_and_rcvd_att_duty(dv)
    ensures inv_active_consensus_instances_imply_delivery_of_att_duties(dv)   
    ensures same_honest_nodes_in_dv_and_ci(dv)    
    ensures assump_construction_of_signed_attestation_signatures(
                dv.construct_signed_attestation_signature,
                dv.dv_pubkey,
                dv.all_nodes)  
    ensures assump_seq_of_att_duties_is_in_order_of_slots(dv.sequence_of_attestation_duties_to_be_served)     
    ensures inv_domain_of_active_consensus_instances_is_subset_of_slashing_db_hist(dv)
    ensures inv_available_current_att_duty_is_latest_att_duty(dv)
    ensures inv_rcvd_attestation_shares_are_sent_messages(dv)
    ensures lem_inv_exists_honest_node_that_sent_att_share_for_every_submitted_att_new_precond(dv)
    ensures inv_data_of_all_created_attestations_is_set_of_decided_values(dv)
    {   
        lem_ind_inv_implies_intermediate_steps_helper_1(dv); 
        lem_ind_inv_implies_intermediate_steps_helper_2(dv);
        lem_ind_inv_implies_intermediate_steps_helper_3(dv);
        lem_ind_inv_implies_intermediate_steps_helper_4(dv);
        lem_inv_every_sent_validity_predicate_is_based_on_existing_slashing_db_and_rcvd_att_duty_ind_inv(dv);
        lem_inv_data_of_all_created_attestations_is_set_of_decided_values_dv_next(dv);
    }
   
    lemma lem_ind_inv_dv_next_inv_all_validity_predicates_are_stored_in_slashing_db_hist(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)  
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')       
    requires ind_inv(dv)
    ensures inv_all_validity_predicates_are_stored_in_slashing_db_hist(dv')
    {
        lem_inv_current_validity_predicate_for_slot_k_is_stored_in_slashing_db_hist_k_inv_active_consensus_instances_predicate_is_in_slashing_db_hist(dv);
        assert inv_active_consensus_instances_predicate_is_in_slashing_db_hist(dv);

        lem_inv_domain_of_active_consensus_instances_is_subset_of_slashing_db_hist(dv);
        assert inv_domain_of_active_consensus_instances_is_subset_of_slashing_db_hist(dv);

        lem_ind_inv_implies_intermediate_steps(dv);
        assert same_honest_nodes_in_dv_and_ci(dv);


        assert && inv_all_validity_predicates_are_stored_in_slashing_db_hist(dv)
               && inv_all_honest_nodes_is_quorum(dv)
               && same_honest_nodes_in_dv_and_ci(dv)
               && inv_only_dv_construct_signed_attestation_signature(dv)    
               && inv_slots_for_sent_validity_predicates_are_stored_in_slashing_db_hist(dv)  
               && inv_domain_of_active_consensus_instances_is_subset_of_slashing_db_hist(dv)
               && inv_active_consensus_instances_predicate_is_in_slashing_db_hist(dv)
               ;

        lem_inv_all_validity_predicates_are_stored_in_slashing_db_hist(dv, e, dv');    
        assert inv_all_validity_predicates_are_stored_in_slashing_db_hist(dv');
    }

    lemma lem_ind_inv_dv_next_inv_exists_honest_node_that_sent_att_share_for_every_submitted_att(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_exists_honest_node_that_sent_att_share_for_every_submitted_att(dv')
    {
        lem_ind_inv_implies_intermediate_steps(dv);
        assert assump_construction_of_signed_attestation_signatures(
                dv.construct_signed_attestation_signature,
                dv.dv_pubkey,
                dv.all_nodes);

        lem_inv_all_in_transit_messages_were_sent_inv_in_transit_messages_are_in_allMessagesSent(dv);
        assert inv_in_transit_messages_are_in_allMessagesSent(dv);

        lem_inv_rcvd_att_shares_are_from_sent_messages_inv_rcvd_attestation_shares_are_sent_messages(dv);
        assert inv_rcvd_attestation_shares_are_sent_messages(dv);

        assert  && Att_DV.next_event(dv, e, dv')
                && inv_exists_honest_node_that_sent_att_share_for_every_submitted_att(dv)
                && assump_construction_of_signed_attestation_signatures(
                    dv.construct_signed_attestation_signature,
                    dv.dv_pubkey,
                    dv.all_nodes
                )
                && inv_only_dv_construct_signed_attestation_signature(dv)  
                && inv_in_transit_messages_are_in_allMessagesSent(dv)
                && inv_all_honest_nodes_is_quorum(dv)
                && inv_rcvd_attestation_shares_are_sent_messages(dv)
                ;

        
        lem_inv_exists_honest_node_that_sent_att_share_for_every_submitted_att_dv_next(dv, e, dv');
        assert inv_exists_honest_node_that_sent_att_share_for_every_submitted_att(dv');
    }

    lemma lem_ind_inv_dv_next_inv_decided_values_of_consensus_instances_are_decided_by_quorum(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_decided_values_of_consensus_instances_are_decided_by_quorum(dv')
    {
        lem_inv_decided_values_of_consensus_instances_are_decided_by_quorum(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_inv_every_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_every_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(dv')
    {
        lem_inv_every_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv_next(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_inv_every_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_every_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(dv')
    {
        lem_inv_every_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_inv_decided_value_of_consensus_instance_for_slot_k_is_for_slot_k(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_decided_value_of_consensus_instance_for_slot_k_is_for_slot_k(dv')
    {
        lem_inv_decided_value_of_consensus_instance_for_slot_k_is_for_slot_k(dv, e, dv');
    }

    
    lemma lem_ind_inv_dv_next_invs_group_8(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_8(dv')
    {
        lem_ind_inv_dv_next_inv_all_validity_predicates_are_stored_in_slashing_db_hist(dv, e, dv');  
        lem_ind_inv_dv_next_inv_exists_honest_node_that_sent_att_share_for_every_submitted_att(dv, e, dv');             
        lem_ind_inv_dv_next_inv_decided_values_of_consensus_instances_are_decided_by_quorum(dv, e, dv');       
        lem_ind_inv_dv_next_inv_every_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(dv, e, dv');  
        lem_ind_inv_dv_next_inv_every_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(dv, e, dv');   
    }

    lemma lem_ind_inv_dv_next_inv_in_transit_messages_are_in_allMessagesSent(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_in_transit_messages_are_in_allMessagesSent(dv')
    {
        lem_inv_all_in_transit_messages_were_sent_dv_next(dv, e, dv');
        lem_inv_all_in_transit_messages_were_sent_inv_in_transit_messages_are_in_allMessagesSent(dv');
    }

    lemma lem_ind_inv_dv_next_inv_38(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_attestation_shares_to_broadcast_are_sent_messages(dv')
    {
        lem_ind_inv_implies_intermediate_steps(dv);
        assert same_honest_nodes_in_dv_and_ci(dv);
        lem_inv_attestation_shares_to_broadcast_are_sent_messages_dv_next(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_inv_exists_att_duty_in_dv_seq_of_att_duties_for_every_slot_in_slashing_db_hist(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_exists_att_duty_in_dv_seq_of_att_duties_for_every_slot_in_slashing_db_hist(dv')
    {
        lem_inv_exists_att_duty_in_dv_seq_of_att_duties_for_every_slot_in_slashing_db_hist(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_invs_group_9(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_9(dv')
    {
        lem_inv_decided_value_of_consensus_instance_for_slot_k_is_for_slot_k(dv, e, dv');
        lem_ind_inv_dv_next_inv_in_transit_messages_are_in_allMessagesSent(dv, e, dv');
        lem_ind_inv_dv_next_inv_38(dv, e, dv');
        lem_inv_attestation_shares_to_broadcast_are_sent_messages_inv_attestation_shares_to_broadcast_is_subset_of_all_messages_sent(dv');
    }

    lemma lem_ind_inv_dv_next_invs_group_10(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_10(dv')
    {        
        lem_ind_inv_dv_next_inv_exists_att_duty_in_dv_seq_of_att_duties_for_every_slot_in_slashing_db_hist(dv, e, dv');
        lem_inv_available_latest_att_duty_is_from_dv_seq_of_att_duties_new_body_dv_next(dv, e, dv');
        lem_inv_slots_of_consensus_instances_are_up_to_slot_of_latest_att_duty_dv_next(dv, e, dv');
        lem_ind_inv_implies_intermediate_steps(dv);
        lem_inv_data_of_att_shares_are_decided_values_dv_next(dv, e, dv');
    }
    
    lemma lem_ind_inv_dv_next_inv_future_decisions_known_by_dvc_are_decisions_of_quorums(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_future_decisions_known_by_dvc_are_decisions_of_quorums(dv')
    {
        lem_ind_inv_implies_intermediate_steps_helper_4(dv);
        assert lem_inv_exists_honest_node_that_sent_att_share_for_every_submitted_att_new_precond(dv);
        lem_inv_future_decisions_known_by_dvc_are_decisions_of_quorums(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_inv_slots_in_future_decided_data_are_correct(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_slots_in_future_decided_data_are_correct(dv')
    {
        lem_ind_inv_implies_intermediate_steps_helper_4(dv);
        lem_inv_slots_in_future_decided_data_are_correct(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_invs_group_11(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_11(dv')
    {
        lem_ind_inv_implies_intermediate_steps_helper_4(dv);
        lem_inv_future_decisions_known_by_dvc_are_decisions_of_quorums(dv, e, dv');
        lem_inv_slots_in_future_decided_data_are_correct(dv, e, dv');        
    }

    lemma lem_ind_inv_dv_next_invs_group_12(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_12(dv')
    {
        lem_ind_inv_implies_intermediate_steps_helper_4(dv);
        lem_inv_sent_validity_predicates_are_only_for_slots_stored_in_slashing_db_hist(dv, e, dv');
        lem_inv_all_validity_predicates_are_stored_in_slashing_db_hist(dv, e, dv');
        lem_inv_every_consensus_instance_condition_for_safety_is_true_dv_next(dv, e, dv');  
        lem_inv_unique_rcvd_att_duty_per_slot_dv_next(dv, e, dv');  
        lem_inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_dv_next(dv, e, dv');  
        lem_inv_no_rcvd_att_duties_are_higher_than_latest_att_duty_dv_next(dv, e, dv');  
    }

    lemma lem_ind_inv_dv_next_invs_group_13(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_13(dv')
    {
        lem_inv_every_decided_data_has_honest_witness_dv_next(dv, e, dv');
        lem_inv_all_created_attestations_are_valid_dv_next(dv, e, dv');
        lem_inv_attestation_is_created_based_on_shares_from_quorum_of_dvc_signer_pubkeys_dv_next(dv, e, dv');
        lem_inv_unchanged_dvc_rs_pubkey_dv_next(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_invs_group_14(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_14(dv')
    {   
        
        lem_assump_seq_of_att_duties_is_in_order_of_slots_dv_next(dv, e, dv');
        lem_inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_dv_next(dv, e, dv');
        lem_inv_sent_att_shares_have_corresponding_slashing_db_attestations_dv_next(dv, e, dv');
        lem_inv_slots_of_consensus_instances_are_up_to_slot_of_latest_att_duty_dv_next(dv, e, dv');
        lem_inv_domain_of_active_consensus_instances_is_subset_of_slashing_db_hist(dv);   
        lem_inv_db_of_vp_contains_all_data_of_sent_att_shares_with_lower_slots_dv_next(dv, e, dv');        
    }
    
    lemma lem_ind_inv_dv_next_ind_inv_helper_1(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_1(dv')
    ensures invs_group_2(dv')
    ensures invs_group_3(dv')
    {
        lem_ind_inv_dv_next_invs_group_1(dv, e, dv');
        lem_ind_inv_dv_next_invs_group_2(dv, e, dv');
        lem_ind_inv_dv_next_invs_group_3(dv, e, dv');
    }

    lemma lem_ind_inv_dv_next_ind_inv_helper_2(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)  
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
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

    lemma lem_ind_inv_dv_next_ind_inv_helper_3(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_9(dv')
    ensures invs_group_10(dv')
    ensures invs_group_11(dv')
    {        
        lem_ind_inv_dv_next_invs_group_9(dv, e, dv');       
        lem_ind_inv_dv_next_invs_group_10(dv, e, dv');  
        lem_ind_inv_dv_next_invs_group_11(dv, e, dv');                                     
    }

    lemma lem_ind_inv_dv_next_ind_inv_helper_4(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_group_12(dv')   
    ensures invs_group_13(dv')    
    ensures invs_group_14(dv')
    {        
        lem_ind_inv_dv_next_invs_group_12(dv, e, dv');                              
        lem_ind_inv_dv_next_invs_group_13(dv, e, dv');     
        lem_ind_inv_dv_next_invs_group_14(dv, e, dv');                              
    }

    lemma lem_ind_inv_dv_next_ind_inv_helper_a(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
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

    lemma lem_ind_inv_dv_next_ind_inv_helper_b(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv) 
    ensures invs_group_9(dv')    
    ensures invs_group_10(dv')    
    ensures invs_group_11(dv')    
    ensures invs_group_12(dv')    
    ensures invs_group_13(dv')    
    ensures invs_group_14(dv')
    {
        lem_ind_inv_dv_next_ind_inv_helper_3(dv, e, dv');   
        lem_ind_inv_dv_next_ind_inv_helper_4(dv, e, dv');    
    }

    lemma lem_ind_inv_dv_next_ind_inv_helper(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
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
    {   
        lem_ind_inv_dv_next_ind_inv_helper_a(dv, e, dv');
        lem_ind_inv_dv_next_ind_inv_helper_b(dv, e, dv');                
    }

    lemma lem_ind_inv_dv_next_ind_inv(dv: AttDVState, e: DVAttestationEvent, dv': AttDVState)       
    requires Att_DV.next_event_preconditions(dv, e)
    requires Att_DV.next_event(dv, e, dv')  
    requires ind_inv(dv)    
    ensures ind_inv(dv')    
    {   
        lem_ind_inv_dv_next_ind_inv_helper(dv, e, dv');                                  
    }

    lemma lem_ind_inv_dv_ind_inv_next_preconditions(dv: AttDVState, dv': AttDVState)       
    requires Att_DV.next_preconditions(dv)
    requires Att_DV.next(dv, dv')  
    requires ind_inv(dv)    
    ensures ind_inv(dv')  
    ensures Att_DV.next_preconditions(dv')
    {
        var e :|
            && preconditions_for_HonestNodeTakingStep(dv, e)
            && next_event(dv, e, dv');

        lem_ind_inv_dv_next_ind_inv(dv, e, dv');
        lem_next_preconditions(dv');
    } 

    lemma lem_next_preconditions(
        s: AttDVState
    )
    requires ind_inv(s)
    ensures  next_preconditions(s)                
    {
        forall event | preconditions_for_HonestNodeTakingStep(s, event)
        ensures next_event_preconditions(s, event);
        {
            if event.HonestNodeTakingStep?
            {

            }
        }

    }     
}