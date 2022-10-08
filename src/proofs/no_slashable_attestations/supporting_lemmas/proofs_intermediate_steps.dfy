include "../../../common/commons.dfy"
include "../common/attestation_creation_instrumented.dfy"
include "../../../specs/consensus/consensus.dfy"
include "../../../specs/network/network.dfy"
include "../../../specs/dv/dv_attestation_creation.dfy"
include "inv.dfy"
include "../../common/helper_sets_lemmas.dfy"


module Proofs_Intermediate_Steps
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB    
    import opened Helper_Sets_Lemmas    
    
    lemma lemma_inv53_ind_inv(dv: DVState)
    requires inv_unchanged_honesty(dv)
    ensures inv53(dv)
    { }
        
    lemma lemma_inv11_ind_inv(
        dv: DVState
    )         
    requires inv_quorum_constraints(dv)      
    requires inv6(dv)    
    requires inv14(dv)
    ensures inv11(dv)
    {   
        var queue := dv.sequence_attestation_duties_to_be_served;
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
    
    lemma lemma_inv12_ind_inv(
        dv: DVState
    )         
    requires inv_quorum_constraints(dv)      
    requires inv7(dv)    
    requires inv14(dv)
    ensures inv12(dv)
    {   
        var queue := dv.sequence_attestation_duties_to_be_served;
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
      
    lemma lemma_inv14_ind_inv(
        dv: DVState
    )    
    requires inv_quorum_constraints(dv)  
    requires inv4(dv)
    requires inv13(dv)
    ensures inv14(dv)    
    {   
        var queue := dv.sequence_attestation_duties_to_be_served;
        var index := dv.index_next_attestation_duty_to_be_served;        
        var next_duty := queue[index].attestation_duty;
        var hn := queue[index].node;

        if hn in dv.honest_nodes_states.Keys 
        {
            var dvc := dv.honest_nodes_states[hn];

            assert inv4_body( hn, dvc.all_rcvd_duties, 
                              dv.sequence_attestation_duties_to_be_served, 
                              dv.index_next_attestation_duty_to_be_served);


            forall rcvd_duty: AttestationDuty | rcvd_duty in dvc.all_rcvd_duties
            ensures rcvd_duty.slot <= next_duty.slot
            {
                
                var k: nat :| && 0 <= k < dv.index_next_attestation_duty_to_be_served
                              && dv.sequence_attestation_duties_to_be_served[k].node == hn
                              && dv.sequence_attestation_duties_to_be_served[k].attestation_duty == rcvd_duty;

                assert dv.sequence_attestation_duties_to_be_served[k].attestation_duty.slot <= next_duty.slot;

                assert rcvd_duty.slot <= next_duty.slot;
            }

            assert inv14_body(dvc, next_duty);
            
        }        
    }

    lemma lemma_concl_future_att_duty_is_higher_than_queued_att_duty_ind_inv(
        dv: DVState
    )    
    requires inv_quorum_constraints(dv)  
    requires inv4(dv)
    requires inv5(dv)
    requires inv13(dv)
    requires inv14(dv)
    ensures concl_future_att_duty_is_higher_than_queued_att_duty(dv)    
    {   
        var queue := dv.sequence_attestation_duties_to_be_served;
        var index := dv.index_next_attestation_duty_to_be_served;        
        var next_duty := queue[index].attestation_duty;
        var hn := queue[index].node;

        if hn in dv.honest_nodes_states.Keys 
        {
            var dvc := dv.honest_nodes_states[hn];

            assert inv4_body(hn, dvc.all_rcvd_duties,
                             dv.sequence_attestation_duties_to_be_served,
                             dv.index_next_attestation_duty_to_be_served);
            assert inv5_body(dvc);
            assert inv14_body(dvc, next_duty);


            forall queued_duty: AttestationDuty | queued_duty in dvc.attestation_duties_queue
            ensures queued_duty.slot <= next_duty.slot
            {
                assert queued_duty in dvc.all_rcvd_duties;
                
                var k: nat :| && 0 <= k < dv.index_next_attestation_duty_to_be_served
                              && dv.sequence_attestation_duties_to_be_served[k].node == hn
                              && dv.sequence_attestation_duties_to_be_served[k].attestation_duty == queued_duty;

                assert dv.sequence_attestation_duties_to_be_served[k].attestation_duty.slot <= next_duty.slot;

                assert queued_duty.slot <= next_duty.slot;
            }

            assert concl_future_att_duty_is_higher_than_queued_att_duty_body(dvc, next_duty);
            
        }        
    }


    lemma lemma_concl_slot_of_active_consensus_instance_is_lower_than_slot_of_queued_att_duty_ind_inv(
        dv: DVState
    )    
    requires inv_queued_att_duty_is_higher_than_latest_served_att_duty(dv)
    requires inv_no_active_consensus_instance_before_receiving_att_duty(dv)
    requires inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty(dv)
    ensures concl_slot_of_active_consensus_instance_is_lower_than_slot_of_queued_att_duty(dv)    
    {   
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys
        {
            var dvc := dv.honest_nodes_states[hn];

            if dvc.latest_attestation_duty.isPresent()
            {
                var latest_duty := dvc.latest_attestation_duty.safe_get();

                forall k: Slot, n: nat | 
                            && k in dvc.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys 
                            && 0 <= n < |dvc.attestation_duties_queue|
                ensures k < dvc.attestation_duties_queue[n].slot;            
                {
                    calc {
                        k; 
                        <= 
                        latest_duty.slot;
                        <
                        dvc.attestation_duties_queue[n].slot;            
                    } 
                }

                assert concl_slot_of_active_consensus_instance_is_lower_than_slot_of_queued_att_duty_body(dvc);
            }
            else
            {
                assert dvc.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys == {};
                assert concl_slot_of_active_consensus_instance_is_lower_than_slot_of_queued_att_duty_body(dvc);
            }
        }
    } 

    lemma lemma_inv51_ind_inv(
        dv: DVState
    )    
    requires inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties(dv)
    ensures inv51(dv)    
    {  
        forall hn: BLSPubkey, s: Slot 
        ensures ( ( && is_honest_node(dv, hn) 
                    && s in dv.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys
                  )
                  ==> inv51_body(dv.honest_nodes_states[hn], s)
                )
        {
            if && is_honest_node(dv, hn) 
               && s in dv.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys
            {
                var hn_state := dv.honest_nodes_states[hn];
                assert inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(hn_state);
                assert inv51_body(hn_state, s);
            }
            else
            {}
        }
            
    } 

    lemma lemma_inv50_ind_inv(
        dv: DVState
    )    
    requires inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred(dv)
    ensures inv50(dv)    
    { 
        forall hn: BLSPubkey, s: Slot, vp: AttestationData -> bool | 
            && is_honest_node(dv, hn)
            && var hn_state := dv.honest_nodes_states[hn];
            && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
            && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s]            
        ensures ( exists duty, db ::
                    && var hn_state := dv.honest_nodes_states[hn];
                    && inv50_body(dv, hn, s, db, duty, vp) 
                )                
        {
            var hn_state := dv.honest_nodes_states[hn];            
            assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(hn_state);
            assert s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
            assert vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s];

            assert ( exists db: set<SlashingDBAttestation>, duty: AttestationDuty ::
                        && duty.slot == s
                        && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
                        && vp == (ad: AttestationData) => consensus_is_valid_attestation_data(db, ad, duty)
                    );

            var db: set<SlashingDBAttestation>, duty: AttestationDuty :|
                        && duty.slot == s
                        && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
                        && vp == (ad: AttestationData) => consensus_is_valid_attestation_data(db, ad, duty)
                    ;

            assert inv50_body(dv, hn, s, db, duty, vp);
        }
    }   

    lemma lemma_inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(
        dv: DVState
    )    
    requires inv_strictly_increasing_queue_of_att_duties(dv)
    requires inv_queued_att_duty_is_higher_than_latest_served_att_duty(dv)
    ensures inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(dv)    
    {}

    lemma lemma_inv_attestation_duty_queue_is_ordered(
        dv: DVState
    )    
    requires inv_strictly_increasing_queue_of_att_duties(dv)    
    ensures inv_attestation_duty_queue_is_ordered(dv)    
    {}

    lemma lemma_pred_inv_current_latest_attestation_duty_match(
        dv: DVState
    )    
    requires inv10(dv)    
    ensures pred_inv_current_latest_attestation_duty_match(dv)    
    {}

    lemma lemma_construct_signed_attestation_signature_assumptions_helper(
        dv: DVState
    )    
    requires inv_construct_signed_attestation_signature_assumptions_helper(dv)    
    ensures construct_signed_attestation_signature_assumptions_helper(
                dv.construct_signed_attestation_signature,
                dv.dv_pubkey,
                dv.all_nodes)    
    {}

    lemma lemma_inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(
        dv: DVState
    )    
    requires inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist(dv)    
    ensures  inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(dv)
    {}

    lemma lemma_inv_rcvd_attn_shares_are_from_sent_messages_pred_rcvd_attestation_shares_is_in_all_messages_sent(
        dv: DVState
    )    
    requires inv_rcvd_attn_shares_are_from_sent_messages(dv)    
    ensures  pred_rcvd_attestation_shares_is_in_all_messages_sent(dv)
    {}

    lemma lemma_inv_attestation_shares_to_broadcast_are_sent_messages_inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(
        dv: DVState
    )
    requires inv_attestation_shares_to_broadcast_are_sent_messages(dv)
    ensures inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(dv)
    {}  

    lemma lemma_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_inv_active_attestation_consensus_instances_predicate_is_in_att_slashing_db_hist(dv: DVState)    
    requires inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k(dv)
    ensures inv_active_attestation_consensus_instances_predicate_is_in_att_slashing_db_hist(dv)
    {}  
    
}