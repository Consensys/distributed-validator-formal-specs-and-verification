include "../../../../common/commons.dfy"
include "../../common/dvc_attestation_creation_instrumented.dfy"
include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_attestation_creation.dfy"


include "../inv.dfy"

module Proofs_Intermediate_Steps
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
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB    
    
    lemma lem_inv_queued_att_duty_is_rcvd_duty3_ind_inv(dv: AttDVState)
    requires inv_unchanged_paras_of_consensus_instances(dv)
    ensures same_honest_nodes_in_dv_and_ci(dv)
    { }
        
    lemma lem_inv_att_duty_in_next_delivery_is_not_lower_than_current_att_duty_ind_inv(
        dv: AttDVState
    )         
    requires inv_all_honest_nodes_is_quorum(dv)      
    requires inv_current_att_duty_is_rcvd_duty(dv)    
    requires inv_att_duty_in_next_delivery_is_not_lower_than_rcvd_att_duties(dv)
    ensures inv_att_duty_in_next_delivery_is_not_lower_than_current_att_duty(dv)
    {   
        var queue := dv.sequence_of_attestation_duties_to_be_served;
        var index := dv.index_next_attestation_duty_to_be_served;        
        var next_duty := queue[index].attestation_duty;
        var hn := queue[index].node;

        if hn in dv.honest_nodes_states.Keys 
        {
            var dvc := dv.honest_nodes_states[hn];
            if dvc.current_attestation_duty.isPresent()
            {
                var duty := dvc.current_attestation_duty.safe_get();
                assert duty in dvc.all_rcvd_duties;  
                assert duty.slot <= next_duty.slot;  
            }
        }
    } 
    
    lemma lem_inv_att_duty_in_next_delivery_is_not_lower_than_latest_att_duty_ind_inv(
        dv: AttDVState
    )         
    requires inv_all_honest_nodes_is_quorum(dv)      
    requires inv_latest_att_duty_is_rcvd_duty(dv)    
    requires inv_att_duty_in_next_delivery_is_not_lower_than_rcvd_att_duties(dv)
    ensures inv_att_duty_in_next_delivery_is_not_lower_than_latest_att_duty(dv)
    {   
        var queue := dv.sequence_of_attestation_duties_to_be_served;
        var index := dv.index_next_attestation_duty_to_be_served;        
        var next_duty := queue[index].attestation_duty;
        var hn := queue[index].node;

        if hn in dv.honest_nodes_states.Keys 
        {
            var dvc := dv.honest_nodes_states[hn];
            if dvc.latest_attestation_duty.isPresent()
            {
                var duty := dvc.latest_attestation_duty.safe_get();
                assert duty in dvc.all_rcvd_duties;  
                assert duty.slot <= next_duty.slot;  
            }
        }
    } 
      
    lemma lem_inv_att_duty_in_next_delivery_is_not_lower_than_rcvd_att_duties_ind_inv(
        dv: AttDVState
    )    
    requires inv_all_honest_nodes_is_quorum(dv)  
    requires assump_seq_of_att_duties_is_in_order_of_slots(dv.sequence_of_attestation_duties_to_be_served)
    requires inv_rcvd_att_duties_are_from_dv_seq_of_att_duties(dv)
    ensures inv_att_duty_in_next_delivery_is_not_lower_than_rcvd_att_duties(dv)    
    {   
        var queue := dv.sequence_of_attestation_duties_to_be_served;
        var index := dv.index_next_attestation_duty_to_be_served;        
        var next_duty := queue[index].attestation_duty;
        var hn := queue[index].node;

        if hn in dv.honest_nodes_states.Keys 
        {
            var dvc := dv.honest_nodes_states[hn];

            forall rcvd_duty: AttestationDuty | rcvd_duty in dvc.all_rcvd_duties
            ensures rcvd_duty.slot <= next_duty.slot
            {
                assert inv_exists_att_duty_in_dv_seq_of_att_duties_for_given_att_duty(
                            rcvd_duty, 
                            hn, 
                            dv.sequence_of_attestation_duties_to_be_served,
                            dv.index_next_attestation_duty_to_be_served);
                
                var k: nat :| && 0 <= k < dv.index_next_attestation_duty_to_be_served
                              && dv.sequence_of_attestation_duties_to_be_served[k].node == hn
                              && dv.sequence_of_attestation_duties_to_be_served[k].attestation_duty == rcvd_duty;

                assert dv.sequence_of_attestation_duties_to_be_served[k].attestation_duty.slot <= next_duty.slot;

                assert rcvd_duty.slot <= next_duty.slot;
            }

            assert inv_att_duty_in_next_delivery_is_not_lower_than_rcvd_att_duties_body(dvc, next_duty);
        }        
    }

    lemma lem_inv_active_consensus_instances_imply_delivery_of_att_duties_ind_inv(
        dv: AttDVState
    )    
    requires inv_slashing_db_hist_keeps_track_only_of_rcvd_att_duties(dv)
    ensures inv_active_consensus_instances_imply_delivery_of_att_duties(dv)    
    {  
        forall hn: BLSPubkey, s: Slot 
        ensures ( ( && is_honest_node(dv, hn) 
                    && s in dv.honest_nodes_states[hn].attestation_consensus_engine_state.slashing_db_hist.Keys
                  )
                  ==> inv_active_consensus_instances_imply_delivery_of_att_duties_body(dv.honest_nodes_states[hn], s)
                )
        {
            if && is_honest_node(dv, hn) 
               && s in dv.honest_nodes_states[hn].attestation_consensus_engine_state.slashing_db_hist.Keys
            {
                var hn_state := dv.honest_nodes_states[hn];
                assert inv_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(hn_state);
                assert inv_active_consensus_instances_imply_delivery_of_att_duties_body(hn_state, s);
            }
            else
            {}
        }
            
    } 

    lemma lem_inv_every_sent_validity_predicate_is_based_on_existing_slashing_db_and_rcvd_att_duty_ind_inv(
        dv: AttDVState
    )    
    requires inv_exist_db_in_slashing_db_hist_and_att_duty_for_every_validity_predicate(dv)
    ensures inv_every_sent_validity_predicate_is_based_on_existing_slashing_db_and_rcvd_att_duty(dv)    
    { 
        forall hn: BLSPubkey, s: Slot, vp: AttestationData -> bool | 
            && is_honest_node(dv, hn)
            && var hn_state := dv.honest_nodes_states[hn];
            && s in hn_state.attestation_consensus_engine_state.slashing_db_hist.Keys
            && vp in hn_state.attestation_consensus_engine_state.slashing_db_hist[s]            
        ensures ( exists duty, db ::
                    && var hn_state := dv.honest_nodes_states[hn];
                    && inv_every_sent_validity_predicate_is_based_on_existing_slashing_db_and_rcvd_att_duty_body(dv, hn, s, db, duty, vp) 
                )                
        {
            var hn_state := dv.honest_nodes_states[hn];            
            assert inv_exist_db_in_slashing_db_hist_and_att_duty_for_every_validity_predicate_body(hn_state);
            assert s in hn_state.attestation_consensus_engine_state.slashing_db_hist.Keys;
            assert vp in hn_state.attestation_consensus_engine_state.slashing_db_hist[s];

            assert ( exists db: set<SlashingDBAttestation>, duty: AttestationDuty ::
                        && duty.slot == s
                        && db in hn_state.attestation_consensus_engine_state.slashing_db_hist[s][vp]
                        && vp == (ad: AttestationData) => ci_decision_att_signature_is_signed_with_pubkey_data(db, ad, duty)
                    );

            var db: set<SlashingDBAttestation>, duty: AttestationDuty :|
                        && duty.slot == s
                        && db in hn_state.attestation_consensus_engine_state.slashing_db_hist[s][vp]
                        && vp == (ad: AttestationData) => ci_decision_att_signature_is_signed_with_pubkey_data(db, ad, duty)
                    ;

            assert inv_every_sent_validity_predicate_is_based_on_existing_slashing_db_and_rcvd_att_duty_body(dv, hn, s, db, duty, vp);
        }
    }   

    lemma lem_inv_available_current_att_duty_is_latest_att_duty(
        dv: AttDVState
    )    
    requires inv_available_current_att_duty_is_latest_att_duty(dv)    
    ensures inv_available_current_att_duty_is_latest_att_duty(dv)    
    {}

    lemma lem_assump_construction_of_signed_attestation_signatures(
        dv: AttDVState
    )    
    requires inv_only_dv_construct_signed_attestation_signatures(dv)    
    ensures assump_construction_of_signed_attestation_signatures(
                dv.construct_signed_attestation_signature,
                dv.dv_pubkey,
                dv.all_nodes)    
    {}

    lemma lem_inv_domain_of_active_consensus_instances_is_subset_of_slashing_db_hist(
        dv: AttDVState
    )    
    requires inv_active_att_consensus_instances_are_tracked_in_slashing_db_hist(dv)    
    ensures  inv_domain_of_active_consensus_instances_is_subset_of_slashing_db_hist(dv)
    {}

    lemma lem_inv_rcvd_att_shares_are_from_sent_messages_inv_rcvd_attestation_shares_are_sent_messages(
        dv: AttDVState
    )    
    requires inv_rcvd_att_shares_are_from_sent_messages(dv)    
    ensures  inv_rcvd_attestation_shares_are_sent_messages(dv)
    {}

    lemma lem_inv_attestation_shares_to_broadcast_are_sent_messages_inv_attestation_shares_to_broadcast_is_subset_of_all_messages_sent(
        dv: AttDVState
    )
    requires inv_attestation_shares_to_broadcast_are_sent_messages(dv)
    ensures inv_attestation_shares_to_broadcast_is_subset_of_all_messages_sent(dv)
    {}  

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_slashing_db_hist_k_inv_active_consensus_instances_predicate_is_in_slashing_db_hist(dv: AttDVState)    
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_slashing_db_hist_k(dv)
    ensures inv_active_consensus_instances_predicate_is_in_slashing_db_hist(dv)
    {}  
    
}