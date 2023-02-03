include "../../../common/commons.dfy"
include "../common/attestation_creation_instrumented.dfy"
include "../../../specs/consensus/consensus.dfy"
include "../../../specs/network/network.dfy"
include "../../../specs/dv/dv_attestation_creation.dfy"
include "../../common/helper_sets_lemmas.dfy"
include "../common/dvc_spec_axioms.dfy"



module Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Spec
    import opened DV
    import opened Helper_Sets_Lemmas
    import opened DVC_Spec_Axioms



    

    predicate is_honest_node(s: DVState, n: BLSPubkey)
    {
        && n in s.honest_nodes_states.Keys
    }

    predicate inv_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(
        dv: DVState,
        dvc: DVCState
    )
    {
        var rcvd_attestation_shares := dvc.rcvd_attestation_shares;

        forall i, j |
            && i in rcvd_attestation_shares.Keys 
            && j in rcvd_attestation_shares[i]
            ::
            rcvd_attestation_shares[i][j] <= dv.att_network.allMessagesSent
    }

    predicate inv_rcvd_attestation_shares_is_in_all_messages_sent_single_node(
        dv: DVState,
        n: BLSPubkey
    )
    requires n in dv.honest_nodes_states.Keys
    {
        inv_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(
            dv,
            dv.honest_nodes_states[n]
        )
    }

    predicate inv_rcvd_attestation_shares_is_in_all_messages_sent(
        dv: DVState    
    )
    {
        forall n |
            n in dv.honest_nodes_states
            ::
            inv_rcvd_attestation_shares_is_in_all_messages_sent_single_node(dv, n)
    }  

    predicate inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(
        dv: DVState,
        hn: BLSPubkey, 
        att_share: AttestationShare,
        a: Attestation
    )
    {
        && hn in dv.honest_nodes_states.Keys 
        && att_share in dv.att_network.allMessagesSent
        && att_share.data == a.data
        && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));
        && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
        && verify_bls_signature(attestation_signing_root, att_share.signature, hn)
    }

    predicate inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv: DVState)
    {
        forall a |
            && a in dv.all_attestations_created
            && is_valid_attestation(a, dv.dv_pubkey)
            ::
            exists hn, att_share: AttestationShare :: inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(dv, hn, att_share, a)
    }

    predicate inv_data_of_att_share_is_decided_value(dv: DVState)
    {
        forall hn, att_share |
                && hn in dv.honest_nodes_states.Keys 
                && att_share in dv.att_network.allMessagesSent
                && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));                
                && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
                && verify_bls_signature(attestation_signing_root, att_share.signature, hn)
            ::
                inv_data_of_att_share_is_decided_value_body(dv, att_share)
    }  

    predicate inv_data_of_att_share_is_decided_value_body(dv: DVState, att_share: AttestationShare)
    {
        && dv.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent()
        && dv.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data
    }  

    predicate inv_decided_value_of_consensus_instance_is_decided_by_quorum(dv: DVState)
    {
        forall cid |
            && cid in dv.consensus_on_attestation_data.Keys
            && dv.consensus_on_attestation_data[cid].decided_value.isPresent()
            ::
            is_a_valid_decided_value(dv.consensus_on_attestation_data[cid])
    }  


    predicate inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(dv: DVState)
    {
        forall cid |
            && cid in dv.consensus_on_attestation_data.Keys
            && dv.consensus_on_attestation_data[cid].decided_value.isPresent()
            ::
            dv.consensus_on_attestation_data[cid].decided_value.safe_get().slot == cid
    }     

    
    predicate inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc(
        dv: DVState,
        n: BLSPubkey,
        cid: Slot
    )
    requires n in dv.honest_nodes_states.Keys 
    requires cid in dv.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances
    {
        var dvc := dv.honest_nodes_states[n];
        var acvc := dvc.attestation_consensus_engine_state.active_attestation_consensus_instances[cid];

        inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_body_body(
            cid, 
            acvc.attestation_duty, 
            acvc.validityPredicate
        ) 
    }

    predicate inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_body(
        dvc: DVCState,
        cid: Slot
    )
    requires cid in dvc.attestation_consensus_engine_state.active_attestation_consensus_instances
    {
        var acvc := dvc.attestation_consensus_engine_state.active_attestation_consensus_instances[cid];
        inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_body_body(
            cid, 
            acvc.attestation_duty, 
            acvc.validityPredicate
        ) 
    }     

    predicate inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_body_body(
        cid: Slot,
        attestation_duty: AttestationDuty,
        vp: AttestationData -> bool
    )
    {
        exists attestation_slashing_db ::
            inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_body(cid, attestation_duty, attestation_slashing_db, vp)        
    }         

    predicate inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2(
        dvc: DVCState
    )
    {
        forall cid | 
            && cid in dvc.attestation_consensus_engine_state.active_attestation_consensus_instances
            ::
            inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_body(dvc, cid)        
    }    

    predicate inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(
        dv: DVState
    )
    {
        forall n, cid | 
            && n in dv.honest_nodes_states 
            && cid in dv.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances
            ::
            inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc(dv, n, cid)
    }

   
    predicate inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_body(
        s: Slot,
        attestation_duty: AttestationDuty,
        attestation_slashing_db: set<SlashingDBAttestation>,
        vp: AttestationData -> bool
    )
    {
        && attestation_duty.slot == s
        && (vp == (ad: AttestationData) => consensus_is_valid_attestation_data(attestation_slashing_db, ad, attestation_duty))
    }

    predicate inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(dv: DVState)
    {
        forall hn, s: Slot, vp |
            && hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
            && vp in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions[hn]
            ::
            exists attestation_duty, attestation_slashing_db ::
                inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_body(s, attestation_duty, attestation_slashing_db, vp)
    }

    predicate inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_dbi(dv: DVState)    
    {
        forall hn, s1: Slot, s2: Slot, vp, db2 |
            && hn in dv.honest_nodes_states.Keys
            && var hn_state := dv.honest_nodes_states[hn];
            && s2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys            
            && s1 < s2
            && hn in dv.consensus_on_attestation_data[s1].honest_nodes_validity_functions.Keys
            && hn in dv.consensus_on_attestation_data[s2].honest_nodes_validity_functions.Keys
            && vp in dv.consensus_on_attestation_data[s2].honest_nodes_validity_functions[hn]        
            && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys   
            && db2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp]          
            && dv.consensus_on_attestation_data[s1].decided_value.isPresent()
            ::                
            && var hn_state := dv.honest_nodes_states[hn];
            && dv.consensus_on_attestation_data[s1].decided_value.isPresent()
            && var decided_att_data := dv.consensus_on_attestation_data[s1].decided_value.safe_get();
            && var sdba := construct_SlashingDBAttestation_from_att_data(decided_att_data);
            && sdba in db2
    }    

    // predicate inv_db_of_validity_predicate_contains_all_previous_decided_values(dv: DVState)    
    // {
    //     forall hn |
    //         && hn in dv.honest_nodes_states.Keys          
    //         ::
    //         inv_queued_att_duties_are_from_dv_seq_of_att_dutiesody(dv, dv.honest_nodes_states[hn])                
    // }   

    // predicate inv_queued_att_duties_are_from_dv_seq_of_att_dutiesody(
    //     dv: DVState, 
    //     hn_state: DVCState
    // )     
    // {
    //     forall s1: Slot, s2: Slot, vp2, db2 |
    //         && s1 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
    //         && s2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys            
    //         && s1 < s2       
    //         && vp2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys   
    //         && db2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp2]           
    //         ::       
    //         inv_queued_att_duties_are_from_dv_seq_of_att_dutiesody_body(dv, s1, db2)           
    // }

    // IMPORTANT: not true in a new version as an honest node might miss some decided attestation data.
    // predicate inv_queued_att_duties_are_from_dv_seq_of_att_dutiesody_body(
    //     dv: DVState, 
    //     s1: Slot,
    //     db2: set<SlashingDBAttestation>
    // ) 
    // {           
    //     && dv.consensus_on_attestation_data[s1].decided_value.isPresent()
    //     && var decided_att_data := dv.consensus_on_attestation_data[s1].decided_value.safe_get();
    //     && var sdba := construct_SlashingDBAttestation_from_att_data(decided_att_data);
    //     && sdba in db2        
    // }    

    predicate inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn],
                dv.index_next_attestation_duty_to_be_served
            )                    
    }       

    predicate inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState,
        index_next_attestation_duty_to_be_served: nat
    )
    {
        forall slot  |
            && slot in n_state.attestation_consensus_engine_state.att_slashing_db_hist
            ::
            exists i: Slot :: 
                && i < index_next_attestation_duty_to_be_served
                && var an := dv.sequence_attestation_duties_to_be_served[i];
                && an.attestation_duty.slot == slot 
                && an.node == n
    }   

    predicate inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(
                dv, 
                hn,
                dv.honest_nodes_states[hn]
            )                    
    }   

    function get_upperlimit_active_instances(
        n_state: DVCState
    ): nat 
    {
        if n_state.latest_attestation_duty.isPresent() then
            n_state.latest_attestation_duty.safe_get().slot + 1
        else
            0
    }                

    predicate inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState
    )
    {
        forall slot  |
            && slot in n_state.attestation_consensus_engine_state.att_slashing_db_hist
            ::
            slot < get_upperlimit_active_instances(n_state)
    }      

    predicate inv_slot_of_consensus_instance_is_up_to_slot_of_latest_attestation_duty_body(
        dvc: DVCState       
    )
    {
        forall slot: Slot |
            && slot in dvc.attestation_consensus_engine_state.att_slashing_db_hist
            ::
            slot < get_upperlimit_active_instances(dvc)
    }     

    predicate inv_slot_of_consensus_instance_is_up_to_slot_of_latest_attestation_duty(
        dv: DVState        
    )
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
                inv_slot_of_consensus_instance_is_up_to_slot_of_latest_attestation_duty_body(dv.honest_nodes_states[hn])        
    }     
    
    // predicate inv_queued_att_duties_are_from_dv_seq_of_att_duties(dv: DVState)    
    // {
    //     forall hn |
    //         && hn in dv.honest_nodes_states.Keys          
    //         ::
    //         inv_queued_att_duties_are_from_dv_seq_of_att_duties_body_body(
    //             dv, 
    //             hn,
    //             dv.honest_nodes_states[hn],
    //             dv.index_next_attestation_duty_to_be_served
    //         )                    
    // }     

    

    // predicate inv_queued_att_duties_are_from_dv_seq_of_att_duties_body_body(
    //     dv: DVState, 
    //     n: BLSPubkey,
    //     n_state: DVCState,
    //     index_next_attestation_duty_to_be_served: nat
    // )
    // {
    //     forall ad  |
    //         && ad in n_state.attestation_duties_queue
    //         ::
    //         exists i: Slot :: 
    //             && i < index_next_attestation_duty_to_be_served
    //             && var an := dv.sequence_attestation_duties_to_be_served[i];
    //             && an.attestation_duty == ad
    //             && an.node == n
    // }   

    

    predicate inv_latest_attestation_duty_is_from_dv_seq_of_att_duties(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_latest_attestation_duty_is_from_dv_seq_of_att_duties_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn],
                dv.index_next_attestation_duty_to_be_served
            )                    
    }               

    predicate inv_latest_attestation_duty_is_from_dv_seq_of_att_duties_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState,
        index_next_attestation_duty_to_be_served: nat
    )
    {
        n_state.latest_attestation_duty.isPresent() ==>
            exists i: Slot :: 
                && i < index_next_attestation_duty_to_be_served
                && var an := dv.sequence_attestation_duties_to_be_served[i];
                && an.attestation_duty == n_state.latest_attestation_duty.safe_get()
                && an.node == n
    }     

    predicate pred_attestation_duty_is_from_dv_seq_of_att_duties_new_body(  
        attestation_duty: AttestationDuty,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    {
        exists i: Slot :: 
            && i < index_next_attestation_duty_to_be_served
            && var an := sequence_attestation_duties_to_be_served[i];
            && an.attestation_duty == attestation_duty
            && an.node == hn
    } 

    predicate inv_available_latest_attestation_duty_is_from_dv_seq_of_att_duties(  
        n: BLSPubkey,
        n_state: DVCState,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    {
        n_state.latest_attestation_duty.isPresent()
        ==>
        exists i: Slot :: 
            && i < index_next_attestation_duty_to_be_served
            && var an := sequence_attestation_duties_to_be_served[i];
            && an.attestation_duty == n_state.latest_attestation_duty.safe_get()
            && an.node == n
    }  

    // predicate inv_queued_att_duties_are_from_dv_seq_of_att_duties_new_body(        
    //     n: BLSPubkey,
    //     n_state: DVCState,
    //     sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
    //     index_next_attestation_duty_to_be_served: nat
    // )
    // {
    //     forall ad  |
    //         && ad in n_state.attestation_duties_queue
    //         ::
    //         exists i: Slot :: 
    //             && i < index_next_attestation_duty_to_be_served
    //             && var an := sequence_attestation_duties_to_be_served[i];
    //             && an.attestation_duty == ad
    //             && an.node == n
    // }          

    function get_upperlimit_decided_instances(
        n_state: DVCState
    ): nat 
    {
        if n_state.latest_attestation_duty.isPresent() then
            if n_state.current_attestation_duty.isPresent() then 
                n_state.latest_attestation_duty.safe_get().slot
            else
                n_state.latest_attestation_duty.safe_get().slot + 1
        else
            0
    }

    // predicate inv_decided_values_of_previous_duties_are_known_new(dv: DVState)    
    // {
    //     forall hn |
    //         && hn in dv.honest_nodes_states.Keys          
    //         ::
    //         inv_decided_values_of_previous_duties_are_known_body_body_new(
    //             dv, 
    //             hn,
    //             dv.honest_nodes_states[hn]
    //         )                    
    // }          

    // predicate inv_decided_values_of_previous_duties_are_known_body_body_new(
    //     dv: DVState, 
    //     n: BLSPubkey,
    //     n_state: DVCState
    // )
    // {
    //     forall an |
    //         && an in dv.sequence_attestation_duties_to_be_served.Values 
    //         && an.node == n 
    //         && an.attestation_duty.slot < get_upperlimit_decided_instances(n_state)
    //     ::
    //         var slot := an.attestation_duty.slot;
    //         && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
    //         // IMPORTANT: The following constraint is not true in a new version.
    //         && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in n_state.attestation_slashing_db
    // }        

    predicate inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn]
            )                    
    }       

    predicate inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState
    )
    {
        forall slot |
            && slot in n_state.future_att_consensus_instances_already_decided.Keys
            ::
            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
            && n_state.future_att_consensus_instances_already_decided[slot] == dv.consensus_on_attestation_data[slot].decided_value.safe_get()
    }  

    predicate inv_slot_in_future_decided_data_is_correct(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_slot_in_future_decided_data_is_correct_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn]
            )                    
    }              

    predicate inv_slot_in_future_decided_data_is_correct_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState
    )
    {
        forall slot |
            && slot in n_state.future_att_consensus_instances_already_decided
            ::
            n_state.future_att_consensus_instances_already_decided[slot].slot == slot
    }       

    // predicate inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(dv: DVState)    
    // {
    //     forall hn |
    //         && hn in dv.honest_nodes_states.Keys          
    //         ::
    //         inv_head_attetation_duty_queue_higher_than_latest_attestation_duty_body_body(
    //             dv.honest_nodes_states[hn]
    //         )                    
    // }                

    // predicate inv_head_attetation_duty_queue_higher_than_latest_attestation_duty_body_body(
    //     n_state: DVCState
    // )
    // {
    //     (
    //         && n_state.attestation_duties_queue != []
    //         && n_state.latest_attestation_duty.isPresent()
    //     ) ==>
    //     n_state.attestation_duties_queue[0].slot > n_state.latest_attestation_duty.safe_get().slot     
    // }

    // predicate inv_attestation_duty_queue_is_ordered(dv: DVState)    
    // {
    //     forall hn |
    //         && hn in dv.honest_nodes_states.Keys          
    //         ::
    //         inv_attestation_duty_queue_is_ordered_body_body(
    //             dv.honest_nodes_states[hn]
    //         )                    
    // }       

    // predicate inv_attestation_duty_queue_is_ordered_body_body(
    //     n_state: DVCState
    // )
    // {
    //     forall i,j | 0 <= i < j < |n_state.attestation_duties_queue| :: n_state.attestation_duties_queue[i].slot <  n_state.attestation_duties_queue[j].slot           
    // }

    // predicate inv_attestation_duty_queue_is_ordered_3(dv: DVState)    
    // {
    //     forall hn |
    //         && hn in dv.honest_nodes_states.Keys          
    //         ::
    //         inv_attestation_duty_queue_is_ordered_3_body_body(
    //             dv, 
    //             hn,
    //             dv.honest_nodes_states[hn]            
    //         )                    
    // }     

    // predicate inv_attestation_duty_queue_is_ordered_3_body_body(
    //     dv: DVState, 
    //     n: BLSPubkey,
    //     n_state: DVCState
    // )
    // {
    //     forall i, k, l, t  |
    //         inv_attestation_duty_queue_is_ordered_3_body_body_premise(
    //             dv,
    //             n, 
    //             n_state,
    //             i,
    //             k, 
    //             l, 
    //             t
    //         )
    //         ::
    //         n_state.attestation_duties_queue[i-1].slot == dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot

    // }       

    // predicate inv_attestation_duty_queue_is_ordered_3_body_body_premise(
    //     dv: DVState, 
    //     n: BLSPubkey,
    //     n_state: DVCState,
    //     i: Slot, 
    //     k: nat,
    //     l: nat, 
    //     t: nat
    // )
    // {
    //         && 0 < i < |n_state.attestation_duties_queue|
    //         && dv.sequence_attestation_duties_to_be_served[k].node == n
    //         && dv.sequence_attestation_duties_to_be_served[l].node == n
    //         && dv.sequence_attestation_duties_to_be_served[t].node == n
    //         && dv.sequence_attestation_duties_to_be_served[k].attestation_duty.slot == n_state.attestation_duties_queue[i-1].slot
    //         && dv.sequence_attestation_duties_to_be_served[l].attestation_duty.slot == n_state.attestation_duties_queue[i].slot
    //         && n_state.attestation_duties_queue[i-1].slot <= dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot < dv.sequence_attestation_duties_to_be_served[l].attestation_duty.slot 
    // } 
        
    // predicate inv_attestation_duty_queue_is_ordered_4(dv: DVState)    
    // {
    //     forall hn |
    //         && hn in dv.honest_nodes_states.Keys          
    //         ::
    //         inv_attestation_duty_queue_is_ordered_4_body_body(
    //             dv, 
    //             hn,
    //             dv.honest_nodes_states[hn],
    //             dv.index_next_attestation_duty_to_be_served
    //         )                    
    // }           

    // predicate inv_attestation_duty_queue_is_ordered_4_body_body(
    //     dv: DVState, 
    //     n: BLSPubkey,
    //     n_state: DVCState,
    //     index_next_attestation_duty_to_be_served: nat
    // )  
    // {
    //     |n_state.attestation_duties_queue| > 0 ==>
    //         forall i |
    //             inv_attestation_duty_queue_is_ordered_4_body_body_premise(
    //                 dv,
    //                 n, 
    //                 n_state,
    //                 i,
    //                 index_next_attestation_duty_to_be_served
    //             )
    //             ::
    //             var last := n_state.attestation_duties_queue[|n_state.attestation_duties_queue|-1];
    //             last.slot == dv.sequence_attestation_duties_to_be_served[i].attestation_duty.slot 

    // }          

    // predicate inv_attestation_duty_queue_is_ordered_4_body_body_premise(
    //     dv: DVState, 
    //     n: BLSPubkey,
    //     n_state: DVCState,
    //     i: Slot, 
    //     index_next_attestation_duty_to_be_served: nat
    // )
    // requires |n_state.attestation_duties_queue| > 0
    // {
    //         var last := n_state.attestation_duties_queue[|n_state.attestation_duties_queue|-1];
    //         && i < index_next_attestation_duty_to_be_served
    //         && dv.sequence_attestation_duties_to_be_served[i].node == n
    //         && last.slot <= dv.sequence_attestation_duties_to_be_served[i].attestation_duty.slot 
    // }       
         

    predicate inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(
                dv.honest_nodes_states[hn]
            )                    
    }       

    predicate inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body
    (
        n_state: DVCState
    )
    {
        n_state.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys <= n_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    }

    predicate inv_active_attestation_consensus_instances_predicate_is_in_att_slashing_db_hist(dv: DVState)    
    {
        forall hn, cid |
            && hn in dv.honest_nodes_states.Keys        
            ::
            inv_active_attestation_consensus_instances_predicate_is_in_att_slashing_db_hist_body(dv.honest_nodes_states[hn], cid)
             
    }       

    predicate inv_active_attestation_consensus_instances_predicate_is_in_att_slashing_db_hist_body
    (
        n_state: DVCState,
        cid: Slot
    )
    {
        && cid in n_state.attestation_consensus_engine_state.active_attestation_consensus_instances 
        ==>
        (
            && cid in n_state.attestation_consensus_engine_state.att_slashing_db_hist
            && n_state.attestation_consensus_engine_state.active_attestation_consensus_instances[cid].validityPredicate in n_state.attestation_consensus_engine_state.att_slashing_db_hist[cid] 
        )
    }    

    predicate inv_current_latest_attestation_duty_match(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_current_latest_attestation_duty_match_body_body(
                dv.honest_nodes_states[hn]
            )                    
    }           

    predicate inv_current_latest_attestation_duty_match_body_body(
        n_state: DVCState
    )
    {
        (
            && n_state.current_attestation_duty.isPresent()
            
        ) ==>
        && n_state.latest_attestation_duty.isPresent()
        && n_state.current_attestation_duty.safe_get() == n_state.latest_attestation_duty.safe_get()
    }

    predicate inv_g_a(dv: DVState)
    {
        forall n | n in dv.honest_nodes_states.Keys :: inv_g_a_body(dv, n)
    }

    predicate inv_g_a_body(
        dv: DVState, 
        n: BLSPubkey
    )
    requires n in dv.honest_nodes_states.Keys 
    {
        var n_state := dv.honest_nodes_states[n];
        inv_g_a_body_body(dv, n, n_state)
    }

    predicate inv_g_a_body_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState
    )
    {
        n_state.latest_attestation_duty.isPresent() ==>
            forall an |
                && an in dv.sequence_attestation_duties_to_be_served.Values 
                && an.node == n 
                && an.attestation_duty.slot < n_state.latest_attestation_duty.safe_get().slot
            ::
                var slot := an.attestation_duty.slot;
                && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
    }         

    // predicate inv_exists_decided_value_for_every_duty_before_queued_duties(dv: DVState)    
    // {
    //     forall hn |
    //         && hn in dv.honest_nodes_states.Keys          
    //         ::
    //         inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(
    //             dv, 
    //             hn,
    //             dv.honest_nodes_states[hn]
    //         )                    
    // }       

    // predicate inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(
    //     dv: DVState, 
    //     n: BLSPubkey,
    //     n_state: DVCState
    // )
    // {
    //     (
    //         &&  |n_state.attestation_duties_queue| > 0 
    //         &&   !n_state.current_attestation_duty.isPresent()
    //     )
    //     ==>
    //         forall an |
    //             && an in dv.sequence_attestation_duties_to_be_served.Values 
    //             && an.node == n 
    //             && an.attestation_duty.slot < n_state.attestation_duties_queue[0].slot
    //         ::
    //             var slot := an.attestation_duty.slot;
    //             && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
    //             && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in n_state.attestation_slashing_db
    // }     

    // predicate inv_g_a_iii(dv: DVState)    
    // {
    //     forall hn |
    //         && hn in dv.honest_nodes_states.Keys          
    //         ::
    //         inv_g_a_iii_body_body(
    //             dv, 
    //             hn,
    //             dv.honest_nodes_states[hn],
    //             dv.index_next_attestation_duty_to_be_served
    //         )                    
    // }  

    // predicate inv_g_a_iii_body_body_helper(
    //     n_state: DVCState,
    //     slot: Slot
    // ) 
    // {
    //     n_state.current_attestation_duty.isPresent() ==>
    //         slot != n_state.current_attestation_duty.safe_get().slot
    // }    

    // predicate inv_g_a_iii_body_body(
    //     dv: DVState, 
    //     n: BLSPubkey,
    //     n_state: DVCState,
    //     index_next_attestation_duty_to_be_served: nat
    // )
    // {
    //     (
    //         &&  |n_state.attestation_duties_queue| == 0 
    //     ) ==>
    //         forall i:nat  |
    //             && i < index_next_attestation_duty_to_be_served
    //             && var an := dv.sequence_attestation_duties_to_be_served[i];
    //             && an.node == n 
    //             && inv_g_a_iii_body_body_helper(n_state, an.attestation_duty.slot)
    //             ::
    //             && var an := dv.sequence_attestation_duties_to_be_served[i];
    //             var slot := an.attestation_duty.slot;
    //             && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
    //             && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in n_state.attestation_slashing_db
    // }  

    // predicate inv_g_a_iii_b_body_body(
    //     dv: DVState, 
    //     n: BLSPubkey,
    //     n_state: DVCState,
    //     index_next_attestation_duty_to_be_served: nat
    // )
    // {
    //     (
    //         &&  |n_state.attestation_duties_queue| == 0 
    //         &&   n_state.current_attestation_duty.isPresent()
    //     ) ==>
    //         forall i:nat  |
    //             && i < index_next_attestation_duty_to_be_served
    //             && var an := dv.sequence_attestation_duties_to_be_served[i];
    //             && an.node == n 
    //             ::
    //             && var an := dv.sequence_attestation_duties_to_be_served[i];
    //             var slot := an.attestation_duty.slot;
    //             && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
    //             && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in n_state.attestation_slashing_db
    // }      

    // predicate inv_g_a_iv_a(dv: DVState)    
    // {
    //     forall hn |
    //         && hn in dv.honest_nodes_states.Keys          
    //         ::
    //         inv_g_a_iv_a_body_body(
    //             dv, 
    //             hn,
    //             dv.honest_nodes_states[hn]
    //         )                    
    // }     

    // predicate inv_g_a_iv_a_body_body(
    //     dv: DVState, 
    //     n: BLSPubkey,
    //     n_state: DVCState
    // )
    // {
    //     (
    //         &&  |n_state.attestation_duties_queue| > 0 
    //         &&   n_state.latest_attestation_duty.isPresent()
    //     )
    //     ==>
    //         forall an |
    //             && an in dv.sequence_attestation_duties_to_be_served.Values 
    //             && an.node == n 
    //             && n_state.latest_attestation_duty.safe_get().slot < an.attestation_duty.slot < n_state.attestation_duties_queue[0].slot
    //         ::
    //             var slot := an.attestation_duty.slot;
    //             && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
    //             && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in n_state.attestation_slashing_db
    // }                  



    // predicate inv_g_c(dv: DVState)
    // {
    //     forall n | n in dv.honest_nodes_states.Keys :: inv_g_c_body(dv, n)
    // }    

    // predicate inv_g_c_body(
    //     dv: DVState, 
    //     n: BLSPubkey
    // )
    // requires n in dv.honest_nodes_states.Keys 
    // {
    //     var n_state := dv.honest_nodes_states[n];
    //     inv_if_has_served_some_duty_then_all_higher_duties_rcvd_from_dv_are_in_the_queue_body_body(dv, n, n_state, dv.index_next_attestation_duty_to_be_served)
    // }

    // predicate inv_if_has_served_some_duty_then_all_higher_duties_rcvd_from_dv_are_in_the_queue_body_body(
    //     dv: DVState, 
    //     n: BLSPubkey,
    //     n_state: DVCState,
    //     index_next_attestation_duty_to_be_served: nat
    // )
    // {
    //     n_state.latest_attestation_duty.isPresent() ==>
    //         forall i:nat  |
    //             && i < index_next_attestation_duty_to_be_served
    //             && var an := dv.sequence_attestation_duties_to_be_served[i];
    //             && an in dv.sequence_attestation_duties_to_be_served.Values 
    //             && an.node == n 
    //             && an.attestation_duty.slot > n_state.latest_attestation_duty.safe_get().slot 
    //             && !dv.consensus_on_attestation_data[an.attestation_duty.slot].decided_value.isPresent()
    //             ::
    //             && var an := dv.sequence_attestation_duties_to_be_served[i];
    //             an.attestation_duty in n_state.attestation_duties_queue
    // }    

    // predicate inv_if_has_not_served_any_duties_then_all_duties_from_dv_are_in_the_queue_body_body(
    //     dv: DVState, 
    //     n: BLSPubkey,
    //     n_state: DVCState,
    //     index_next_attestation_duty_to_be_served: nat
    // )
    // {
    //     !n_state.latest_attestation_duty.isPresent() ==>
    //         forall i:nat  |
    //             && i < index_next_attestation_duty_to_be_served
    //             && var an := dv.sequence_attestation_duties_to_be_served[i];
    //             && an in dv.sequence_attestation_duties_to_be_served.Values 
    //             && an.node == n 
    //             && !dv.consensus_on_attestation_data[an.attestation_duty.slot].decided_value.isPresent()
    //             ::
    //             && var an := dv.sequence_attestation_duties_to_be_served[i];
    //             an.attestation_duty in n_state.attestation_duties_queue
    // }    


    predicate inv_slot_in_future_decided_data_is_correctody_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState
    )
    {
        forall slot |
            && slot in n_state.future_att_consensus_instances_already_decided
            ::
            dv.consensus_on_attestation_data[slot].decided_value.isPresent()
    }    


    // predicate inv_only_joins_consensus_instances_if_received_att_duties_body(dv: DVState, hn: BLSPubkey, s: Slot)
    // {
    //     && is_honest_node(dv, hn)
    //     && var hn_state := dv.honest_nodes_states[hn];
    //     && ( s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    //          ==> 
    //          exists duty: AttestationDuty :: duty in hn_state.all_rcvd_duties && duty.slot == s
    //        )
    // }

    // predicate inv_only_joins_consensus_instances_if_received_att_duties(dv: DVState)
    // {
    //     forall hn: BLSPubkey, s: Slot | is_honest_node(dv, hn) ::
    //         inv_only_joins_consensus_instances_if_received_att_duties_body(dv, hn, s)
    // }  

    predicate inv_rcvd_att_duty_is_from_dv_seq_for_rcvd_att_duty_body(
        dvc: DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    {
       forall att_duty |
            att_duty in dvc.all_rcvd_duties
            ::
            inv_rcvd_att_duty_is_from_dv_seq_for_rcvd_att_duty_body_body(                
                att_duty, 
                hn, 
                sequence_attestation_duties_to_be_served,
                index_next_attestation_duty_to_be_served)
    }

    predicate inv_rcvd_att_duty_is_from_dv_seq_for_rcvd_att_duty_body_body(        
        att_duty: AttestationDuty,
        hn: BLSPubkey, 
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    {
            exists i ::
                && 0 <= i
                && i < index_next_attestation_duty_to_be_served 
                && var duty_and_node := sequence_attestation_duties_to_be_served[i];
                && duty_and_node.node == hn
                && duty_and_node.attestation_duty == att_duty
    }

    predicate inv_rcvd_att_duty_is_from_dv_seq_for_rcvd_att_duty(dv: DVState)
    {
        forall hn: BLSPubkey | 
            is_honest_node(dv, hn) 
            ::
            && var hn_state := dv.honest_nodes_states[hn];
            && inv_rcvd_att_duty_is_from_dv_seq_for_rcvd_att_duty_body(                    
                    hn_state, 
                    hn, 
                    dv.sequence_attestation_duties_to_be_served,
                    dv.index_next_attestation_duty_to_be_served)
    }  

    // predicate inv_queued_att_duty_is_dvn_seq_of_att_duty3_body_a(dv: DVState, hn: BLSPubkey, s: Slot)
    // requires is_honest_node(dv, hn)
    // requires s in dv.consensus_on_attestation_data.Keys         
    // requires hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys      
    // requires && inv_only_joins_consensus_instances_if_received_att_duties_body(dv, hn, s) 
    //          && inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv) 
    // {    
    //     && var hn_state := dv.honest_nodes_states[hn];        
    //     && var duty: AttestationDuty :| duty in hn_state.all_rcvd_duties && duty.slot == s;        
    //     && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys                
    //     && (forall vp, db |
    //             && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s].Keys 
    //             && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
    //             ::
    //             && db <= hn_state.attestation_slashing_db                    
    //        )        
    // }

    // predicate inv_queued_att_duty_is_dvn_seq_of_att_duty3_body_b(
    //     dv: DVState, 
    //     hn: BLSPubkey, 
    //     s: Slot, 
    //     ci: ConsensusInstance<AttestationData>, 
    //     h_nodes: set<BLSPubkey>
    // )
    // requires is_honest_node(dv, hn)
    // requires s in dv.consensus_on_attestation_data.Keys         
    // requires hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys      
    // requires ( && inv_only_joins_consensus_instances_if_received_att_duties_body(dv, hn, s) 
    //            && inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv) 
    //          )
    // requires s in dv.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys                
    // requires is_a_valid_decided_value_according_to_set_of_nodes(ci, h_nodes)
    // {
    //     && var hn_state := dv.honest_nodes_states[hn];        
    //     && var duty: AttestationDuty :| duty in hn_state.all_rcvd_duties && duty.slot == s;        
    //     && ( && dv.consensus_on_attestation_data[s].decided_value.isPresent()
    //          && hn in h_nodes
    //             ==> 
    //             && var ad := dv.consensus_on_attestation_data[s].decided_value.safe_get();
    //             && exists vp, db :: && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s].Keys 
    //                                 && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
    //                                 && consensus_is_valid_attestation_data(db, ad, duty)    
    //        )
    // }

    // predicate inv_queued_att_duty_is_dvn_seq_of_att_duty3(dv: DVState)
    // {
    //     forall hn: BLSPubkey, s: Slot |            
    //         && is_honest_node(dv, hn)
    //         && var hn_state := dv.honest_nodes_states[hn];
    //         && s in dv.consensus_on_attestation_data.Keys
    //         && hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys      
    //         && inv_only_joins_consensus_instances_if_received_att_duties_body(dv, hn, s) 
    //         && inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv)           
    //         ::            
    //         && inv_queued_att_duty_is_dvn_seq_of_att_duty3_body_a(dv, hn, s)
    //         && ( dv.consensus_on_attestation_data[s].decided_value.isPresent() 
    //              ==> exists h_nodes :: && is_a_valid_decided_value_according_to_set_of_nodes(
    //                                             dv.consensus_on_attestation_data[s], 
    //                                             h_nodes) 
    //                                    && inv_queued_att_duty_is_dvn_seq_of_att_duty3_body_b(dv, hn, s, dv.consensus_on_attestation_data[s], h_nodes)
    //            )                          
    // }   

    predicate has_all_slashing_db_attestations_before_slot_s(
        db: set<SlashingDBAttestation>,
        S: set<SlashingDBAttestation>,
        s: Slot
    )
    requires (forall r: SlashingDBAttestation :: 
                    r in db ==> (exists data: AttestationData :: r.signing_root == Some(hash_tree_root(data))))
    {
        && S <= db
        && ( forall r | r in db && r !in S :: get_slot_from_slashing_db_attestation(r) >= s )
        && ( forall r | r in S :: get_slot_from_slashing_db_attestation(r) < s )
    }

    // predicate inv_queued_att_duty_is_dvn_seq_of_att_duty4_body(dv: DVState, hn: BLSPubkey, s1: Slot, s2: Slot, vp1: AttestationData -> bool, vp2: AttestationData -> bool, db2: set<SlashingDBAttestation>)
    // requires is_honest_node(dv, hn)
    // requires && var hn_state: DVCState := dv.honest_nodes_states[hn];
    //          && s1 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    //          && s2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
    //          && s1 < s2
    //          && vp1 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s1].Keys
    //          && vp2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys
    // requires && var hn_state: DVCState := dv.honest_nodes_states[hn];
    //         && ( forall db, r: SlashingDBAttestation |
    //                 && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s1][vp1]
    //                 && r in db
    //                 :: 
    //                     (exists data: AttestationData :: r.signing_root == Some(hash_tree_root(data))) )
    // {
    //     forall T |
    //     && var hn_state: DVCState := dv.honest_nodes_states[hn];
    //     && T in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s1][vp1]
    //     ::
    //     && var db1: set<SlashingDBAttestation> :| has_all_slashing_db_attestations_before_slot_s(T, db1, s2);
    //     && db1 <= db2   
    // }

    // predicate inv_queued_att_duty_is_dvn_seq_of_att_duty4(dv: DVState)
    // {
    //     forall hn: BLSPubkey | is_honest_node(dv, hn) ::
    //         && var hn_state := dv.honest_nodes_states[hn];
    //         && forall s1: Slot, s2: Slot, vp1, vp2, db2 |
    //                 && s1 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    //                 && s2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
    //                 && s1 < s2
    //                 && vp1 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s1].Keys
    //                 && vp2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys
    //                 && db2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp2]
    //                 && ( forall db, r: SlashingDBAttestation |
    //                         && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s1][vp1]
    //                         && r in db
    //                         :: 
    //                             (exists data: AttestationData :: r.signing_root == Some(hash_tree_root(data))) )
    //                 ::
    //                 inv_queued_att_duty_is_dvn_seq_of_att_duty4_body(dv, hn, s1, s2, vp1, vp2, db2)
                    
    // }  


    // predicate inv_queued_att_duty_is_dvn_seq_of_att_duty5(dv: DVState)
    // {
    //     forall hn: BLSPubkey | is_honest_node(dv, hn) ::
    //         && var hn_state := dv.honest_nodes_states[hn];
    //         && forall s: Slot, vp, db | 
    //             && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    //             && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s]
    //             && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
    //             ::
    //                 db <= hn_state.attestation_slashing_db
    // }  

    predicate inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv: DVState)
    {
        forall hn: BLSPubkey, s: Slot | is_honest_node(dv, hn) ::
            && var hn_state := dv.honest_nodes_states[hn];
            && ( hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
                 ==> 
                 s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys)
    }

    predicate inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body(
        dv: DVState, 
        hn: BLSPubkey,
        hn_state: DVCState,
        s: Slot,
        vp: AttestationData -> bool
    )
    requires hn in dv.honest_nodes_states.Keys
    {
        (
            && var hn_state := dv.honest_nodes_states[hn];
            && hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
            && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
            && vp in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions[hn]
        )
            ==>
        (
            && var hn_state := dv.honest_nodes_states[hn];
            && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s]   
        )             
    }       
    
    predicate inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv: DVState)
    {
        forall hn: BLSPubkey, s: Slot, vp : AttestationData -> bool |
            hn in dv.honest_nodes_states.Keys
            ::
            inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body(
                dv,
                hn,
                dv.honest_nodes_states[hn],
                s,
                vp
            )
    }              

    predicate safety(dv: DVState)
    {
        forall a: Attestation ::
            a in dv.globally_signed_attestations 
                ==> 
                (
                    && var S := dv.globally_signed_attestations - { a };
                    && !is_slashable_attestation_data_in_set_of_attestations(S, a.data)
                )
    }

    predicate inv_queued_att_duty_is_dvn_seq_of_att_duty1<D(!new, 0)>(ci: ConsensusInstance<D>)
    {
        ci.decided_value.isPresent()
        <==> 
        is_a_valid_decided_value(ci)            
    }

    predicate honest_nodes_with_validityPredicate(consa: ConsensusInstance<AttestationData>,  h_nodes_a: set<BLSPubkey>)
    requires h_nodes_a <= consa.honest_nodes_validity_functions.Keys  
    requires |h_nodes_a| >= quorum(|consa.all_nodes|) 
                                        - (|consa.all_nodes| - |consa.honest_nodes_status.Keys|)
    requires consa.decided_value.isPresent()
    {
        forall n | n in h_nodes_a 
            :: exists vp: AttestationData -> bool | vp in consa.honest_nodes_validity_functions[n] 
                    :: vp(consa.decided_value.safe_get())
    }
    
    predicate inv_exists_honest_node_that_contributed_to_decisions_of_consensus_instances(
        dv: DVState, 
        a: Attestation, a': Attestation, 
        m: BLSPubkey,
        consa: ConsensusInstance<AttestationData>, consa': ConsensusInstance<AttestationData>,
        h_nodes_a: set<BLSPubkey>, h_nodes_a': set<BLSPubkey>)
    {
        && is_honest_node(dv, m)                
        && consa == dv.consensus_on_attestation_data[a.data.slot]
        && consa' == dv.consensus_on_attestation_data[a'.data.slot]
        && m in consa.honest_nodes_validity_functions.Keys
        && m in h_nodes_a
        && m in consa'.honest_nodes_validity_functions.Keys                
        && m in h_nodes_a'
        && consa'.honest_nodes_validity_functions[m] != {}
        && is_a_valid_decided_value_according_to_set_of_nodes(consa, h_nodes_a) 
        && is_a_valid_decided_value_according_to_set_of_nodes(consa', h_nodes_a') 
    }

    predicate inv_unique_rcvd_att_duty_per_slot(dv: DVState)
    {
        forall hn: BLSPubkey | 
            is_honest_node(dv, hn) 
            ::
            inv_unique_rcvd_att_duty_per_slot_body(dv.honest_nodes_states[hn])
    }

    predicate inv_unique_rcvd_att_duty_per_slot_body(dvc: DVCState)
    {
        forall d1: AttestationDuty, d2: AttestationDuty | 
            && d1 in dvc.all_rcvd_duties
            && d2 in dvc.all_rcvd_duties
            && d1.slot == d2.slot
            ::
            d1 == d2
    }

    predicate inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_att_duty_body(
        dv: DVState, 
        hn: BLSPubkey, 
        s: Slot, 
        db: set<SlashingDBAttestation>, 
        duty: AttestationDuty, 
        vp: AttestationData -> bool)
    requires && is_honest_node(dv, hn)
             && var hn_state := dv.honest_nodes_states[hn];
             && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
             && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s]
    {
        && var hn_state := dv.honest_nodes_states[hn];
        && duty.slot == s
        && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
        && vp == (ad: AttestationData) => consensus_is_valid_attestation_data(db, ad, duty)
    }

    predicate inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_att_duty(dv: DVState)
    {
        forall hn: BLSPubkey, s: Slot, vp: AttestationData -> bool | 
            && is_honest_node(dv, hn)
            && var hn_state := dv.honest_nodes_states[hn];
            && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
            && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s]
            ::
            exists duty, db ::
                && var hn_state := dv.honest_nodes_states[hn];
                && inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_att_duty_body(dv, hn, s, db, duty, vp)
    }

    
    // TODO
    // predicate inv_decided_data_has_an_honest_witness_body<D(!new, 0)>(ci: ConsensusInstance, hn: BLSPubkey) 
    // {
    //     && hn in ci.honest_nodes_validity_functions.Keys
    //     && ci.honest_nodes_validity_functions[hn] != {}                
    // }
    
    predicate inv_decided_data_has_an_honest_witness_body<D(!new, 0)>(ci: ConsensusInstance) 
    {
        ci.decided_value.isPresent()
        ==> 
        is_a_valid_decided_value(ci)
    }
    
    predicate inv_decided_data_has_an_honest_witness(dv: DVState)
    {
        forall s: Slot ::
            && var ci := dv.consensus_on_attestation_data[s];
            && inv_decided_data_has_an_honest_witness_body(ci)
            // && ( ci.decided_value.isPresent()
            //      ==> 
            //      is_a_valid_decided_value(ci)
                // //  ( exists nodes :: 
                // //             && is_a_valid_decided_value_according_to_set_of_nodes(ci, nodes)            
                //             // && ( forall hn: BLSPubkey :: 
                //             //             && is_honest_node(dv, hn)
                //             //             && hn in nodes
                //             //             ==> 
                //             //             inv_decided_data_has_an_honest_witness_body(ci, hn)                                        
                //             //     )
                // //  )
                              
            //    )
    }


    predicate same_honest_nodes_in_dv_and_ci(dv: DVState)
    {
        forall s: Slot ::
            && var ci := dv.consensus_on_attestation_data[s];            
            && dv.all_nodes == ci.all_nodes
            && dv.honest_nodes_states.Keys == ci.honest_nodes_status.Keys
    }
    

    predicate inv_quorum_constraints(dv: DVState)
    {        
        && var all_nodes := dv.all_nodes;
        && var honest_nodes := dv.honest_nodes_states.Keys;
        && var dishonest_nodes := dv.adversary.nodes;
        && 0 < |all_nodes|
        && quorum(|all_nodes|) <= |honest_nodes|
        && |dishonest_nodes| <= f(|all_nodes|) 
        && all_nodes == honest_nodes + dishonest_nodes
        && honest_nodes * dishonest_nodes == {}
    }

    predicate inv_unchanged_paras_of_consensus_instances(dv: DVState)
    {
        forall ci | ci in dv.consensus_on_attestation_data.Values
            :: && ci.all_nodes == dv.all_nodes
               && ci.honest_nodes_status.Keys == dv.honest_nodes_states.Keys  
               && ci.honest_nodes_status.Keys <= ci.all_nodes
               && ci.honest_nodes_validity_functions.Keys <= ci.honest_nodes_status.Keys
               && |ci.all_nodes - ci.honest_nodes_status.Keys| <= f(|ci.all_nodes|)
    }

    predicate inv_only_dv_construct_signed_attestation_signature(dv: DVState)
    {
        && construct_signed_attestation_signature_assumptions(dv)                
        && forall n | n in dv.honest_nodes_states.Keys :: 
                && var nodes := dv.honest_nodes_states[n];
                && nodes.construct_signed_attestation_signature == dv.construct_signed_attestation_signature
                && nodes.dv_pubkey == dv.dv_pubkey       
                && nodes.peers == dv.all_nodes
    }

    // predicate old_inv_queued_att_duty_is_dvn_seq_of_att_duty_body(dv: DVState, n: BLSPubkey, dvc: DVCState)    
    // requires n in dv.honest_nodes_states.Keys
    // requires dvc == dv.honest_nodes_states[n]
    // {
    //     forall duty: AttestationDuty | duty in dvc.all_rcvd_duties ::
    //             exists k: nat :: 
    //                 && 0 <= k < dv.index_next_attestation_duty_to_be_served
    //                 && dv.sequence_attestation_duties_to_be_served[k].node == n
    //                 && dv.sequence_attestation_duties_to_be_served[k].attestation_duty == duty
    // }

    // predicate old_inv_queued_att_duty_is_dvn_seq_of_att_duty(dv: DVState)
    // {
    //     forall n: BLSPubkey | n in dv.honest_nodes_states.Keys ::            
    //         && var dvc := dv.honest_nodes_states[n];
    //         && old_inv_queued_att_duty_is_dvn_seq_of_att_duty_body(dv, n, dvc)
    // }


    // predicate inv_queued_att_duty_is_dvn_seq_of_att_duty_body(
    //     hn: BLSPubkey, 
    //     all_rcvd_duties: set<AttestationDuty>, 
    //     seq_att_duties: iseq<AttestationDutyAndNode>,
    //     len: nat
    // )    
    // {
    //     forall duty: AttestationDuty | duty in all_rcvd_duties ::
    //         exists k: nat :: 
    //             && 0 <= k < len
    //             && seq_att_duties[k].node == hn
    //             && seq_att_duties[k].attestation_duty == duty
    // }

    // predicate inv_queued_att_duty_is_dvn_seq_of_att_duty(dv: DVState)
    // {
    //     forall n: BLSPubkey | n in dv.honest_nodes_states.Keys ::            
    //         && var dvc := dv.honest_nodes_states[n];
    //         && inv_queued_att_duty_is_dvn_seq_of_att_duty_body(
    //                 n, 
    //                 dvc.all_rcvd_duties, 
    //                 dv.sequence_attestation_duties_to_be_served,
    //                 dv.index_next_attestation_duty_to_be_served)
    // }

    // predicate inv_queued_att_duty_is_rcvd_duty_body(dvc: DVCState)
    // {
    //     forall k: nat ::
    //         0 <= k < |dvc.attestation_duties_queue|
    //             ==> ( && var queued_duty: AttestationDuty := dvc.attestation_duties_queue[k];
    //                   && queued_duty in dvc.all_rcvd_duties )
    // }

    // predicate inv_queued_att_duty_is_rcvd_duty(dv: DVState)
    // {
    //     forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
    //         && var dvc := dv.honest_nodes_states[hn];
    //         && inv_queued_att_duty_is_rcvd_duty_body(dvc)
    // }

    predicate inv_current_att_duty_is_rcvd_duty_body(dvc: DVCState)
    {
        dvc.current_attestation_duty.isPresent()
        ==> 
        dvc.current_attestation_duty.safe_get() in dvc.all_rcvd_duties
    }

    predicate inv_current_att_duty_is_rcvd_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_current_att_duty_is_rcvd_duty_body(dvc)
    }

    predicate inv_latest_served_duty_is_rcvd_duty_body(dvc: DVCState)
    {
        dvc.latest_attestation_duty.isPresent()
        ==> 
        dvc.latest_attestation_duty.safe_get() in dvc.all_rcvd_duties
    }

    predicate inv_latest_served_duty_is_rcvd_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_latest_served_duty_is_rcvd_duty_body(dvc)
    }

    predicate inv_none_latest_served_duty_implies_none_current_att_duty_body(dvc: DVCState)
    {
        !dvc.latest_attestation_duty.isPresent()
        ==> 
        !dvc.current_attestation_duty.isPresent()
    }

    predicate inv_none_latest_served_duty_implies_none_current_att_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_none_latest_served_duty_implies_none_current_att_duty_body(dvc)
    }
  
    predicate inv_current_att_duty_is_either_none_or_latest_served_duty_body(dvc: DVCState)
    {
        !dvc.latest_attestation_duty.isPresent()
        ==> 
        ( || !dvc.current_attestation_duty.isPresent()
          || ( && dvc.latest_attestation_duty.isPresent()
               && dvc.current_attestation_duty.isPresent()
               && dvc.current_attestation_duty.safe_get()
                    == dvc.latest_attestation_duty.safe_get()
             )
        )
    }

    predicate inv_current_att_duty_is_either_none_or_latest_served_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_current_att_duty_is_either_none_or_latest_served_duty_body(dvc)
    }

    predicate inv_available_current_att_duty_is_latest_served_att_duty_body(dvc: DVCState)
    {
        dvc.current_attestation_duty.isPresent()
        ==> 
        ( && dvc.latest_attestation_duty.isPresent()
          && dvc.current_attestation_duty.safe_get()
                                == dvc.latest_attestation_duty.safe_get()                   
        )
    }

    predicate inv_available_current_att_duty_is_latest_served_att_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_available_current_att_duty_is_latest_served_att_duty_body(dvc)
    }

    predicate inv_att_duty_in_next_delivery_is_not_lower_than_current_att_duty_body(dvc: DVCState, next_duty: AttestationDuty)
    {
        dvc.current_attestation_duty.isPresent()
        ==> 
        dvc.current_attestation_duty.safe_get().slot <= next_duty.slot        
    }

    predicate inv_att_duty_in_next_delivery_is_not_lower_than_current_att_duty(dv: DVState)
    {
        && var dv_duty_queue := dv.sequence_attestation_duties_to_be_served;
        && var dv_index := dv.index_next_attestation_duty_to_be_served;
        && var next_duty_and_node := dv_duty_queue[dv_index];
        && forall hn: BLSPubkey | 
            && hn in dv.honest_nodes_states.Keys
            && hn == next_duty_and_node.node 
            ::            
            && var dvc := dv.honest_nodes_states[hn];
            && var next_duty := next_duty_and_node.attestation_duty;
            && inv_att_duty_in_next_delivery_is_not_lower_than_current_att_duty_body(dvc, next_duty)
    }

    predicate inv_att_duty_in_next_delivery_is_not_lower_than_latest_served_att_duty_body(dvc: DVCState, next_duty: AttestationDuty)
    {
        dvc.latest_attestation_duty.isPresent()
        ==> 
        dvc.latest_attestation_duty.safe_get().slot <= next_duty.slot        
    }

    predicate inv_att_duty_in_next_delivery_is_not_lower_than_latest_served_att_duty(dv: DVState)
    {
        && var dv_duty_queue := dv.sequence_attestation_duties_to_be_served;
        && var dv_index := dv.index_next_attestation_duty_to_be_served;
        && var next_duty_and_node := dv_duty_queue[dv_index];
        && forall hn: BLSPubkey | 
            && hn in dv.honest_nodes_states.Keys
            && hn == next_duty_and_node.node 
            ::            
            && var dvc := dv.honest_nodes_states[hn];
            && var next_duty := next_duty_and_node.attestation_duty;
            && inv_att_duty_in_next_delivery_is_not_lower_than_latest_served_att_duty_body(dvc, next_duty)
    }

    predicate inv_is_sequence_attestation_duties_to_be_serves_orders(dv: DVState)
    {
        inv_sequence_attestation_duties_to_be_served_orderd(dv)
    }

    predicate inv_att_duty_in_next_delivery_is_not_lower_than_rcvd_att_duties_body(dvc: DVCState, next_duty: AttestationDuty)
    {
       forall rcvd_duty: AttestationDuty | rcvd_duty in dvc.all_rcvd_duties ::
            rcvd_duty.slot <= next_duty.slot        
    }

    predicate inv_att_duty_in_next_delivery_is_not_lower_than_rcvd_att_duties(dv: DVState)
    {
        && var dv_duty_queue := dv.sequence_attestation_duties_to_be_served;
        && var dv_index := dv.index_next_attestation_duty_to_be_served;
        && var next_duty_and_node := dv_duty_queue[dv_index];
        && forall hn: BLSPubkey | 
            && hn in dv.honest_nodes_states.Keys
            && hn == next_duty_and_node.node 
            ::            
            && var dvc := dv.honest_nodes_states[hn];
            && var next_duty := next_duty_and_node.attestation_duty;
            && inv_att_duty_in_next_delivery_is_not_lower_than_rcvd_att_duties_body(dvc, next_duty)
    }

    // predicate concl_future_att_duty_is_higher_than_queued_att_duty_body(dvc: DVCState, next_duty: AttestationDuty)
    // {
    //    forall rcvd_duty: AttestationDuty | rcvd_duty in dvc.attestation_duties_queue ::
    //         rcvd_duty.slot < next_duty.slot        
    // }

    // predicate concl_future_att_duty_is_higher_than_queued_att_duty(dv: DVState)
    // {
    //     && var dv_duty_queue := dv.sequence_attestation_duties_to_be_served;
    //     && var dv_index := dv.index_next_attestation_duty_to_be_served;
    //     && var next_duty_and_node := dv_duty_queue[dv_index];
    //     && forall hn: BLSPubkey | 
    //         && hn in dv.honest_nodes_states.Keys
    //         && hn == next_duty_and_node.node 
    //         ::            
    //         && var dvc := dv.honest_nodes_states[hn];
    //         && var next_duty := next_duty_and_node.attestation_duty;
    //         && concl_future_att_duty_is_higher_than_queued_att_duty_body(dvc, next_duty)
    // }

    // predicate inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(dvc: DVCState)
    // {
    //     !dvc.latest_attestation_duty.isPresent()
    //         ==> |dvc.attestation_duties_queue| == 0
    // }

    // predicate inv_no_queued_att_duty_if_latest_served_att_duty_is_none(dv: DVState)
    // {
    //     forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
    //         && var dvc := dv.honest_nodes_states[hn];
    //         && inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(dvc)
    // }

    // predicate inv_strictly_increasing_queue_of_att_duties_body(dvc: DVCState)
    // {
    //     && var queue := dvc.attestation_duties_queue;
    //     && ( forall k1: Slot, k2: Slot |
    //             &&  0 <= k1
    //             &&  k1 < k2
    //             &&  k2 < |queue|
    //             ::
    //                 queue[k1].slot < queue[k2].slot
    //        )
    // }

    // predicate inv_strictly_increasing_queue_of_att_duties(dv: DVState)
    // {
    //     forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
    //         && var dvc := dv.honest_nodes_states[hn];
    //         && inv_strictly_increasing_queue_of_att_duties_body(dvc)
    // }

    // predicate inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(dvc: DVCState)
    // {
    //     && var queue := dvc.attestation_duties_queue;
    //     && dvc.latest_attestation_duty.isPresent()
    //     ==>
    //     && ( forall k: nat |
    //             &&  0 <= k
    //             &&  k < |queue|                
    //             ::
    //             dvc.latest_attestation_duty.safe_get().slot < queue[k].slot 
    //        )
    // }

    // predicate inv_queued_att_duty_is_higher_than_latest_served_att_duty(dv: DVState)
    // {
    //     forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
    //         && var dvc := dv.honest_nodes_states[hn];
    //         && inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(dvc)
    // }

    predicate invNetwork(
        dv: DVState
    )
    {
         forall m | 
                && m in dv.att_network.messagesInTransit
            ::
                m.message in dv.att_network.allMessagesSent       
    }



    predicate inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent_single_node(
        dv: DVState,
        n: BLSPubkey
    )
    requires n in dv.honest_nodes_states.Keys 
    {
        dv.honest_nodes_states[n].attestation_shares_to_broadcast.Values <= dv.att_network.allMessagesSent
    }

    predicate inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(
        dv: DVState
    )
    {
        forall n |
            n in dv.honest_nodes_states.Keys 
            ::
        inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent_single_node(dv, n)
    }    

    predicate inv_no_duplicated_att_duties(dv: DVState)
    {        
        && ( forall k1: Slot, k2: Slot ::
                && 0 <= k1
                && k1 < k2
                && dv.sequence_attestation_duties_to_be_served[k1].node 
                        in dv.honest_nodes_states.Keys
                && dv.sequence_attestation_duties_to_be_served[k1].node 
                        == dv.sequence_attestation_duties_to_be_served[k2].node 
                ==> 
                && var duty1 := dv.sequence_attestation_duties_to_be_served[k1].attestation_duty;
                && var duty2 := dv.sequence_attestation_duties_to_be_served[k2].attestation_duty;
                && duty1.slot < duty2.slot
           )
    }

    predicate pred_unchanged_dvn_seq_of_att_duties(dv: DVState, dv': DVState)
    {
        dv.sequence_attestation_duties_to_be_served
                == dv'.sequence_attestation_duties_to_be_served
    }

    predicate inv_every_att_duty_before_dvn_att_index_was_delivered_body(dvc: DVCState, duty: AttestationDuty)
    {
        duty in dvc.all_rcvd_duties
    }

    predicate inv_every_att_duty_before_dvn_att_index_was_delivered(dv: DVState)
    {
        forall k: nat ::
            && 0 <= k < dv.index_next_attestation_duty_to_be_served
            && dv.sequence_attestation_duties_to_be_served[k].node in dv.honest_nodes_states.Keys
            ==> 
            && var duty_and_node: AttestationDutyAndNode := dv.sequence_attestation_duties_to_be_served[k];
            && var duty := duty_and_node.attestation_duty;
            && var hn := duty_and_node.node;
            && var dvc := dv.honest_nodes_states[hn];
            && inv_every_att_duty_before_dvn_att_index_was_delivered_body(dvc, duty)
    }    

    predicate inv_no_active_consensus_instance_before_receiving_an_att_duty_body(dvc: DVCState)
    {
        !dvc.latest_attestation_duty.isPresent()
        ==> 
        dvc.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys == {}
    }

    predicate inv_no_active_consensus_instance_before_receiving_an_att_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_no_active_consensus_instance_before_receiving_an_att_duty_body(dvc)
    }
    
    predicate inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body(dvc: DVCState)
    {
        dvc.latest_attestation_duty.isPresent()
        ==> ( forall k: Slot | k in dvc.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys 
                ::
                k <= dvc.latest_attestation_duty.safe_get().slot
            )
    }

    predicate inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_att_duty_body(dvc)
    }

    // predicate concl_slot_of_active_consensus_instance_is_lower_than_slot_of_queued_att_duty_body(dvc: DVCState)
    // {
    //     dvc.latest_attestation_duty.isPresent()
    //     ==> ( forall k: Slot, n: nat | 
    //             && k in dvc.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys 
    //             && 0 <= n < |dvc.attestation_duties_queue|
    //             ::
    //             k <= dvc.attestation_duties_queue[n].slot
    //         )
    // }

    // predicate concl_slot_of_active_consensus_instance_is_lower_than_slot_of_queued_att_duty(dv: DVState)
    // {
    //     forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
    //         && var dvc := dv.honest_nodes_states[hn];
    //         && concl_slot_of_active_consensus_instance_is_lower_than_slot_of_queued_att_duty_body(dvc)
    // }

    predicate inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(dvc: DVCState)
    {
        forall k: Slot | k in dvc.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys ::
            exists rcvd_duty: AttestationDuty :: 
                && rcvd_duty in dvc.all_rcvd_duties
                && rcvd_duty.slot == k
    }

    predicate inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(dvc)
    }

    predicate inv_consensus_instances_only_for_rcvd_duties_body(dvc: DVCState)
    {
        forall k: Slot | k in dvc.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys 
            ::
            && dvc.attestation_consensus_engine_state.active_attestation_consensus_instances[k].attestation_duty in dvc.all_rcvd_duties                
            && dvc.attestation_consensus_engine_state.active_attestation_consensus_instances[k].attestation_duty.slot == k
    }

    predicate inv_consensus_instances_only_for_rcvd_duties(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_consensus_instances_only_for_rcvd_duties_body(dvc)
    }

    predicate inv_active_consensus_instances_implied_the_delivery_of_att_duties_body(hn_state: DVCState, s: Slot)
    requires s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    {
        exists duty: AttestationDuty :: 
                    && duty in hn_state.all_rcvd_duties
                    && duty.slot == s
    }


    predicate inv_active_consensus_instances_implied_the_delivery_of_att_duties(dv: DVState)
    {
        forall hn: BLSPubkey, s: Slot ::
            ( && is_honest_node(dv, hn) 
              && var hn_state := dv.honest_nodes_states[hn];
              && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
            )
            ==>
            inv_active_consensus_instances_implied_the_delivery_of_att_duties_body(dv.honest_nodes_states[hn], s)                
    }

    predicate inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(hn_state: DVCState)    
    {
        forall k: Slot | k in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys ::
            exists duty: AttestationDuty :: 
                    && duty in hn_state.all_rcvd_duties
                    && duty.slot == k
    }

    predicate inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties(dv: DVState)
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            && var hn_state := dv.honest_nodes_states[hn];            
            && inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(hn_state)       
    }

    predicate inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate_body_ces(ces: ConsensusEngineState)
    {
        forall s: Slot, vp: AttestationData -> bool |
                ( && s in ces.att_slashing_db_hist.Keys
                  && vp in ces.att_slashing_db_hist[s]
                )
                :: 
                ( exists db: set<SlashingDBAttestation>, duty: AttestationDuty ::
                        && duty.slot == s
                        && db in ces.att_slashing_db_hist[s][vp]
                        && vp == (ad: AttestationData) => consensus_is_valid_attestation_data(db, ad, duty)
                )
    }

    predicate inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate_body(hn_state: DVCState)
    {
        forall s: Slot, vp: AttestationData -> bool |
                ( && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                  && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s]
                )
                :: 
                ( exists db: set<SlashingDBAttestation>, duty: AttestationDuty ::
                        && duty.slot == s
                        && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
                        && vp == (ad: AttestationData) => consensus_is_valid_attestation_data(db, ad, duty)
                )
    }

    predicate inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate(dv: DVState)
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate_body(dvc)
    }

    predicate inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(hn_state: DVCState)
    {
        forall k: Slot |
            k in hn_state.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys ::
                && var ci := hn_state.attestation_consensus_engine_state.active_attestation_consensus_instances[k];
                && var vp: AttestationData -> bool := ci.validityPredicate;
                && k in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
                && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[k].Keys             
    }

    predicate inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k(dv: DVState)
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(dvc)
    }

    predicate inv_monotonic_att_slashing_db_body(dvc: DVCState, dvc': DVCState)
    {
        dvc.attestation_slashing_db <= dvc'.attestation_slashing_db
    }

    predicate inv_monotonic_att_slashing_db(dv: DVState, event: DV.Event, dv': DVState)    
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            && hn in dv'.honest_nodes_states
            && var dvc := dv.honest_nodes_states[hn];
            && var dvc' := dv'.honest_nodes_states[hn];
            && inv_monotonic_att_slashing_db_body(dvc, dvc')
    }

    predicate inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(ces: ConsensusEngineState, attestation_slashing_db: set<SlashingDBAttestation>)
    {
        forall s: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation> |
                ( && s in ces.att_slashing_db_hist.Keys
                  && vp in ces.att_slashing_db_hist[s]
                  && db in ces.att_slashing_db_hist[s][vp]
                )
                :: 
                db <= attestation_slashing_db
    }

    predicate inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(hn_state: DVCState)
    {
        forall s: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation> |
                ( && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                  && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s]
                  && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
                )
                :: 
                db <= hn_state.attestation_slashing_db
    }

    predicate inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db(dv: DVState)
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(dvc)
    }

    predicate inv_monotonic_att_slashing_db_hist_body(dvc: DVCState, dvc': DVCState)
    {        
        dvc.attestation_consensus_engine_state.att_slashing_db_hist.Keys
        <= 
        dvc'.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    }

    predicate inv_monotonic_att_slashing_db_hist(dv: DVState, event: DV.Event, dv': DVState)    
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            && hn in dv'.honest_nodes_states
            && var dvc := dv.honest_nodes_states[hn];
            && var dvc' := dv'.honest_nodes_states[hn];
            && inv_monotonic_att_slashing_db_hist_body(dvc, dvc')
    }

    predicate prop_monotonic_set_of_in_transit_messages(dv: DVState, dv': DVState)
    {
        && dv.att_network.allMessagesSent <= dv'.att_network.allMessagesSent
    }
     
   
    predicate inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_body(dvc: DVCState)
    {
        dvc.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys 
        <= 
        dvc.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    } 

    predicate inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist(dv: DVState)
    {
        forall hn | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_body(dvc)
    } 

    predicate inv_construct_signed_attestation_signature_assumptions_helper(dv: DVState)
    {
        construct_signed_attestation_signature_assumptions_helper(
            dv.construct_signed_attestation_signature,
            dv.dv_pubkey,
            dv.all_nodes)
    }

    predicate inv_all_in_transit_messages_were_sent_body<M>(e: Network<M>)
    {
         forall m | m in e.messagesInTransit::
                m.message in e.allMessagesSent       
    } 
     
    predicate inv_all_in_transit_messages_were_sent(dv: DVState)
    {
         forall m | m in dv.att_network.messagesInTransit::
                m.message in dv.att_network.allMessagesSent       
    } 

    predicate inv_rcvd_attn_shares_are_from_sent_messages_body(
        dv: DVState,
        dvc: DVCState
    )
    {
        var rcvd_attestation_shares := dvc.rcvd_attestation_shares;

        forall i, j |
            && i in rcvd_attestation_shares.Keys 
            && j in rcvd_attestation_shares[i]
            ::
            rcvd_attestation_shares[i][j] <= dv.att_network.allMessagesSent
    }    

    predicate inv_rcvd_attn_shares_are_from_sent_messages(
        dv: DVState    
    )
    {
        forall n | n in dv.honest_nodes_states ::
            && var dvc := dv.honest_nodes_states[n];
            && inv_rcvd_attn_shares_are_from_sent_messages_body(dv, dvc)
    } 


    predicate inv_attestation_shares_to_broadcast_are_sent_messages_body(
        dv: DVState,
        dvc: DVCState
    )    
    {
        dvc.attestation_shares_to_broadcast.Values <= dv.att_network.allMessagesSent
    }

    predicate inv_attestation_shares_to_broadcast_are_sent_messages(
        dv: DVState
    )
    {
        forall n | n in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[n];
            && inv_attestation_shares_to_broadcast_are_sent_messages_body(dv, dvc)
    }

    predicate inv39(
        dv: DVState,        
        dv': DVState
    )       
    {
        dv.att_network.allMessagesSent <= dv'.att_network.allMessagesSent
    }

    
    predicate inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist_body(
        dv: DVState, 
        hn: BLSPubkey,
        hn_state: DVCState,
        s: Slot
    )
    {
        hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
        ==> s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    }

    predicate inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist(dv: DVState)
    {
        forall hn: BLSPubkey, s: Slot |
            hn in dv.honest_nodes_states
            :: 
            inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist_body(dv, hn, dv.honest_nodes_states[hn], s)        
    } 

    predicate inv_no_active_consensus_instance_before_receiving_att_duty_body(dvc: DVCState)
    {
        !dvc.latest_attestation_duty.isPresent()
        ==> dvc.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys == {}
    }

    predicate inv_no_active_consensus_instance_before_receiving_att_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_no_active_consensus_instance_before_receiving_att_duty_body(dvc)
    }

    predicate inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(dvc: DVCState)
    {
        dvc.latest_attestation_duty.isPresent()
        ==> ( forall k: Slot | k in dvc.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys 
                ::
                k <= dvc.latest_attestation_duty.safe_get().slot
            )
    }

    predicate inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(dvc)
    }

    predicate inv_consensus_instances_are_isConditionForSafetyTrue(dv: DVState)
    {
        forall slot: Slot | slot in dv.consensus_on_attestation_data.Keys  ::
                    isConditionForSafetyTrue(dv.consensus_on_attestation_data[slot])                    
    }

    predicate pred_last_att_duty_is_delivering_to_given_honest_node(
        attestation_duty: AttestationDuty,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    {
        && 0 < index_next_attestation_duty_to_be_served 
        && var i := index_next_attestation_duty_to_be_served - 1;
        && var an := dv.sequence_attestation_duties_to_be_served[i];
        && an.attestation_duty == attestation_duty
        && an.node == n
    }

    predicate inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_body(dvc: DVCState)
    {
        !dvc.latest_attestation_duty.isPresent()
        <==> 
        dvc.all_rcvd_duties == {}
    }

    predicate inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_body(dv.honest_nodes_states[hn])
    }

    predicate inv_no_rcvd_att_duty_is_higher_than_latest_att_duty_body(dvc: DVCState)
    {
        dvc.latest_attestation_duty.isPresent()
        ==>
        ( forall att_duty | att_duty in dvc.all_rcvd_duties ::
            att_duty.slot <= dvc.latest_attestation_duty.safe_get().slot
        )
    }

    predicate inv_no_rcvd_att_duty_is_higher_than_latest_att_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            &&  var dvc := dv.honest_nodes_states[hn];
            &&  inv_no_rcvd_att_duty_is_higher_than_latest_att_duty_body(dvc)
    }

   // predicate inv_data_of_all_created_attestations_is_set_of_decided_values_2(dv: DVState)
    // {
    //     forall slot | slot in dv.consensus_on_attestation_data.Keys ::
    //             && var consa := dv.consensus_on_attestation_data[slot];
    //             && consa.decided_value.isPresent()
    //             ==>
    //             exists a | a in dv.all_attestations_created ::
    //                     a.data == consa.decided_value.safe_get() 
    // }

    // TODO
    predicate inv_data_of_all_created_attestations_is_set_of_decided_values(dv: DVState)
    {
        forall a | a in dv.all_attestations_created ::
                && var consa := dv.consensus_on_attestation_data[a.data.slot];
                && consa.decided_value.isPresent() 
                && a.data == consa.decided_value.safe_get() 
    }

    predicate inv_one_honest_dvc_is_required_to_pass_signer_threshold(
        dv: DVState,
        signers: set<BLSPubkey>,
        att_shares: set<AttestationShare>,
        signing_root: Root
    )
    {
        (
            && signer_threshold(signers, att_shares, signing_root)
            && signers <= dv.all_nodes
        )
        ==>
        (
            exists h_node ::
                && h_node in signers
                && is_honest_node(dv, h_node)
        )
    }

    predicate inv_all_created_attestations_are_valid(dv: DVState)
    {
        forall a | a in dv.all_attestations_created ::
                is_valid_attestation(a, dv.dv_pubkey)
    }

    predicate inv_outputs_attestations_submited_are_valid(
        outputs: Outputs,
        dv_pubkey: BLSPubkey)
    {
        forall submitted_attestation | submitted_attestation in outputs.attestations_submitted ::
            is_valid_attestation(submitted_attestation, dv_pubkey)
    }

    predicate pred_slashing_db_attestation_in_two_dbs(
        sdba: SlashingDBAttestation,
        db1: set<SlashingDBAttestation>,
        db2: set<SlashingDBAttestation>
    )
    {
        && sdba in db1
        && sdba in db2
    }

    predicate inv_slashing_db_att_in_db_for_low_slot_is_in_db_for_high_slot_body_helper(
                set_db:  set<set<SlashingDBAttestation>>,
                set_db':  set<set<SlashingDBAttestation>>
    )
    {
        forall db, db', sdba |
            && db in set_db
            && db' in set_db'
            ::
            (   sdba in db
                ==>
                sdba in db'
            )
    }

    predicate inv_slashing_db_att_in_db_for_low_slot_is_in_db_for_high_slot_body_body(
        db_hist_on_slot: map<AttestationData -> bool, set<set<SlashingDBAttestation>>>,
        db_hist_on_slot': map<AttestationData -> bool, set<set<SlashingDBAttestation>>>
    )
    {
        forall vp, vp' |
            && vp in db_hist_on_slot.Keys
            && vp' in db_hist_on_slot'.Keys 
            ::
            inv_slashing_db_att_in_db_for_low_slot_is_in_db_for_high_slot_body_helper(
                db_hist_on_slot[vp],
                db_hist_on_slot'[vp']
            )
             
    }

    predicate inv_slashing_db_att_in_db_for_low_slot_is_in_db_for_high_slot_body(
        dvc: DVCState
    )
    {
        forall slot:Slot, slot': Slot | 
            && slot in dvc.attestation_consensus_engine_state.att_slashing_db_hist.Keys
            && slot' in dvc.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
            && slot < slot'
            ::
            inv_slashing_db_att_in_db_for_low_slot_is_in_db_for_high_slot_body_body(
                 dvc.attestation_consensus_engine_state.att_slashing_db_hist[slot], 
                 dvc.attestation_consensus_engine_state.att_slashing_db_hist[slot']
            )
    }

    predicate inv_slashing_db_att_in_db_for_low_slot_is_in_db_for_high_slot(
        dv: DVState
    )
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            inv_slashing_db_att_in_db_for_low_slot_is_in_db_for_high_slot_body(dv.honest_nodes_states[hn])
        
    }

    predicate pred_verify_owner_of_attestation_share_with_bls_signature(
        rs_pubkey: BLSPubkey,
        att_share: AttestationShare
    )
    {
        && var decided_attestation_data := att_share.data;
        && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
        && var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
        && verify_bls_signature(attestation_signing_root, att_share.signature, rs_pubkey)
    }

    predicate pred_is_owner_of_one_attestaion_share_in_set_of_shares(
        rs_pubkey: BLSPubkey,
        attestation_shares: set<AttestationShare>
    )
    {
        exists share | share in attestation_shares ::
            pred_verify_owner_of_attestation_share_with_bls_signature(rs_pubkey, share)
    }

    predicate pred_attestation_is_created_based_on_sent_attestation_shares(
        dv: DVState,
        attestation: Attestation,
        attestation_shares: set<AttestationShare>
    )
    {
        && attestation_shares <= dv.att_network.allMessagesSent
        && var constructed_sig := dv.construct_signed_attestation_signature(attestation_shares);
        && constructed_sig.isPresent()
        && constructed_sig.safe_get() == attestation.signature
        && do_all_att_shares_have_the_same_data(attestation_shares, attestation.data)
    }

    predicate inv_exists_honest_node_that_contributed_to_creation_of_two_submitted_attestations_body(
        dv: DVState,
        a: Attestation, 
        a': Attestation
    )
    {
        exists hn: BLSPubkey, att_shares: set<AttestationShare>, att_shares': set<AttestationShare> ::
            && is_honest_node(dv, hn)
            && var rs_pubkey: BLSPubkey := dv.honest_nodes_states[hn].rs.pubkey;
            && pred_attestation_is_created_based_on_sent_attestation_shares(dv, a, att_shares)            
            && pred_is_owner_of_one_attestaion_share_in_set_of_shares(rs_pubkey, att_shares)
            && pred_attestation_is_created_based_on_sent_attestation_shares(dv, a', att_shares')
            && pred_is_owner_of_one_attestaion_share_in_set_of_shares(rs_pubkey, att_shares')
    }

    predicate inv_exists_honest_node_that_contributed_to_creation_of_two_submitted_attestations(
        dv: DVState)
    {
        forall a: Attestation, a': Attestation |
            && a in dv.all_attestations_created
            && a' in dv.all_attestations_created
            ::
            inv_exists_honest_node_that_contributed_to_creation_of_two_submitted_attestations_body(dv, a, a')
    }
    
    predicate inv_if_honest_node_sends_att_share_it_receives_att_data_before_body(
        dvc: DVCState,
        att_share: AttestationShare
    )
    {
        && var att_data: AttestationData := att_share.data;
        && var slot: Slot := att_data.slot;
        && var slashing_db_attestation := SlashingDBAttestation(
                                            source_epoch := att_data.source.epoch,
                                            target_epoch := att_data.target.epoch,
                                            signing_root := Some(hash_tree_root(att_data)));
        && slashing_db_attestation in dvc.attestation_slashing_db
        && exists att_duty: AttestationDuty, vp: AttestationData -> bool :: 
                (   && att_duty in dvc.all_rcvd_duties
                    && slot in dvc.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                    && vp in dvc.attestation_consensus_engine_state.att_slashing_db_hist[slot].Keys
                    // && consensus_is_valid_attestation_data(dvc.attestation_slashing_db, att_data, att_duty)
                    && vp(att_data)
                )
    }

    predicate inv_if_honest_node_sends_att_share_it_receives_att_data_before(dv: DVState)
    {
        forall hn, att_share |
            && is_honest_node(dv, hn)
            && att_share in dv.att_network.allMessagesSent
            && var rs_pubkey: BLSPubkey := dv.honest_nodes_states[hn].rs.pubkey;
            && pred_verify_owner_of_attestation_share_with_bls_signature(rs_pubkey, att_share)
            ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_if_honest_node_sends_att_share_it_receives_att_data_before_body(dvc, att_share)
    }

    predicate inv_data_of_sent_att_shares_is_known_body(
        dvc: DVCState,
        att_share: AttestationShare
    )
    {
        && var att_data: AttestationData := att_share.data;
        && var slot: Slot := att_data.slot;
        && var slashing_db_attestation := SlashingDBAttestation(
                                            source_epoch := att_data.source.epoch,
                                            target_epoch := att_data.target.epoch,
                                            signing_root := Some(hash_tree_root(att_data)));
        && slashing_db_attestation in dvc.attestation_slashing_db
        && exists att_duty: AttestationDuty, vp: AttestationData -> bool :: 
                (   && att_duty in dvc.all_rcvd_duties
                    && slot in dvc.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                    && vp in dvc.attestation_consensus_engine_state.att_slashing_db_hist[slot].Keys
                    // && consensus_is_valid_attestation_data(dvc.attestation_slashing_db, att_data, att_duty)
                    && vp(att_data)
                )
    }

    predicate inv_outputs_attestation_shares_sent_is_tracked_in_attestation_slashing_db_body(
        dvc: DVCState, 
        att_share: AttestationShare
    )
    {
        && var att_data: AttestationData := att_share.data;
        && var slashing_db_attestation := construct_SlashingDBAttestation_from_att_data(att_data);
        && slashing_db_attestation in dvc.attestation_slashing_db  
        && var rs_pubkey: BLSPubkey := dvc.rs.pubkey;    
        && pred_verify_owner_of_attestation_share_with_bls_signature(rs_pubkey, att_share)
    }   

    predicate inv_outputs_attestation_shares_sent_is_tracked_in_attestation_slashing_db(
        outputs: Outputs,
        dvc: DVCState)
    {
        forall att_share: AttestationShare | 
            att_share in getMessagesFromMessagesWithRecipient(outputs.att_shares_sent) 
            ::
            inv_outputs_attestation_shares_sent_is_tracked_in_attestation_slashing_db_body(dvc, att_share)
    } 

    predicate inv_att_shares_to_broadcast_is_tracked_in_attestation_slashing_db_body(
        dvc: DVCState
    )
    {
        forall slot: Slot | 
            slot in dvc.attestation_shares_to_broadcast.Keys
            ::
            && var att_share: AttestationShare := dvc.attestation_shares_to_broadcast[slot];
            && var att_data: AttestationData := att_share.data;
            && var slashing_db_attestation := construct_SlashingDBAttestation_from_att_data(att_data);
            && slashing_db_attestation in dvc.attestation_slashing_db  
            && var rs_pubkey: BLSPubkey := dvc.rs.pubkey;    
            && pred_verify_owner_of_attestation_share_with_bls_signature(rs_pubkey, att_share)
    }   

    predicate inv_att_shares_to_broadcast_is_tracked_in_attestation_slashing_db(
        dv: DVState)
    {
        forall hn: BLSPubkey | 
            is_honest_node(dv, hn)
            ::
            inv_att_shares_to_broadcast_is_tracked_in_attestation_slashing_db_body(dv.honest_nodes_states[hn])
    } 

    predicate inv_data_of_att_shares_is_known_body(
        dvc: DVCState,
        att_share: AttestationShare
    )
    {
        && var att_data := att_share.data;
        && var slashing_db_attestation := construct_SlashingDBAttestation_from_att_data(att_data);
        && slashing_db_attestation in dvc.attestation_slashing_db     
    }

    predicate inv_data_of_att_shares_is_known(
        dv: DVState
    )
    {
        forall hn: BLSPubkey, att_share: AttestationShare | 
            && is_honest_node(dv, hn)
            && att_share in dv.att_network.allMessagesSent 
            && var dvc: DVCState := dv.honest_nodes_states[hn];
            && var rs_pubkey: BLSPubkey := dvc.rs.pubkey;
            && pred_verify_owner_of_attestation_share_with_bls_signature(rs_pubkey, att_share)
            ::
            && var dvc: DVCState := dv.honest_nodes_states[hn];
            && inv_data_of_att_shares_is_known_body(dvc, att_share)            
    }

    predicate inv_attestation_is_created_with_shares_from_quorum_body_signers_helper(
        att_shares: set<AttestationShare>,
        dvc: DVCState
    )
    {
        exists att_share: AttestationShare ::
            && att_share in att_shares
            && var rs_pubkey := dvc.rs.pubkey;
            && pred_verify_owner_of_attestation_share_with_bls_signature(rs_pubkey, att_share)
    }

    predicate inv_attestation_is_created_with_shares_from_quorum_body_signers(
        dv: DVState,
        att_shares: set<AttestationShare>,
        dvc_signer_pubkeys: set<BLSPubkey>
    )
    {
        forall key: BLSPubkey | key in dvc_signer_pubkeys ::
            key in dv.honest_nodes_states.Keys
            ==>
            inv_attestation_is_created_with_shares_from_quorum_body_signers_helper(
                    att_shares,
                    dv.honest_nodes_states[key]
                )        
    }

    predicate inv_attestation_is_created_with_shares_from_quorum_body_helper(
        dv: DVState, 
        att: Attestation,
        att_shares: set<AttestationShare>, 
        signers: set<BLSPubkey>
    )
    {
        && att_shares <= dv.att_network.allMessagesSent
        && var constructed_sig := dv.construct_signed_attestation_signature(att_shares);
        && constructed_sig.isPresent()
        && constructed_sig.safe_get() == att.signature
        && do_all_att_shares_have_the_same_data(att_shares, att.data)
        && signers <= dv.all_nodes
        && inv_attestation_is_created_with_shares_from_quorum_body_signers(dv, att_shares, signers)
        && |signers| >= quorum(|dv.all_nodes|)
    }

    predicate inv_attestation_is_created_with_shares_from_quorum_body(
        dv: DVState, 
        att: Attestation        
    )
    {
        exists att_shares, dvc_signer_pubkeys :: 
                // inv_attestation_is_created_with_shares_from_quorum_body_helper(dv, att, att_shares, signers)                
                && att_shares <= dv.att_network.allMessagesSent
                && var constructed_sig := dv.construct_signed_attestation_signature(att_shares);
                && constructed_sig.isPresent()
                && constructed_sig.safe_get() == att.signature
                && do_all_att_shares_have_the_same_data(att_shares, att.data)
                && dvc_signer_pubkeys <= dv.all_nodes
                && inv_attestation_is_created_with_shares_from_quorum_body_signers(dv, att_shares, dvc_signer_pubkeys)
                && |dvc_signer_pubkeys| >= quorum(|dv.all_nodes|)
    }

    predicate inv_attestation_is_created_with_shares_from_quorum(dv: DVState)
    {
        forall att: Attestation | att in dv.all_attestations_created ::
                inv_attestation_is_created_with_shares_from_quorum_body(dv, att)
    }

    predicate inv_attestation_is_created_with_shares_from_quorum_rs_signers_body(
        att_shares: set<AttestationShare>,
        rs_signer_pubkey: BLSPubkey
    )
    {
        exists att_share: AttestationShare ::
            && att_share in att_shares
            && pred_verify_owner_of_attestation_share_with_bls_signature(rs_signer_pubkey, att_share)
    }

    predicate inv_attestation_is_created_with_shares_from_quorum_rs_signers(
        att_shares: set<AttestationShare>,
        rs_signer_pubkeys: set<BLSPubkey>
    )
    {
        forall key: BLSPubkey | key in rs_signer_pubkeys ::
                inv_attestation_is_created_with_shares_from_quorum_rs_signers_body(
                    att_shares,
                    key
                )        
    }

    predicate inv_outputs_attestations_submited_is_created_with_shares_from_quorum_body(
        dvc: DVCState, 
        att: Attestation
    )
    {
        && att.data.slot in dvc.rcvd_attestation_shares.Keys
        && exists att_shares, rs_signer_pubkeys, k ::          
                && k in dvc.rcvd_attestation_shares[att.data.slot].Keys
                && att_shares <= dvc.rcvd_attestation_shares[att.data.slot][k]
                && var constructed_sig := dvc.construct_signed_attestation_signature(att_shares);
                && constructed_sig.isPresent()
                && constructed_sig.safe_get() == att.signature
                && do_all_att_shares_have_the_same_data(att_shares, att.data)
                && inv_attestation_is_created_with_shares_from_quorum_rs_signers(att_shares, rs_signer_pubkeys)
                && |rs_signer_pubkeys| >= quorum(|dvc.peers|)
                && rs_signer_pubkeys <= dvc.peers
    }   

    predicate inv_outputs_attestations_submited_is_created_with_shares_from_quorum(
        outputs: Outputs,
        dvc: DVCState)
    {
        forall submitted_attestation | submitted_attestation in outputs.attestations_submitted ::
            inv_outputs_attestations_submited_is_created_with_shares_from_quorum_body(dvc, submitted_attestation)
    } 

    predicate pred_intersection_of_honest_nodes_in_two_quorum_contains_an_honest_node(
        dv: DVState,
        h_nodes_1: set<BLSPubkey>,
        h_nodes_2: set<BLSPubkey>
    )
    {
        && h_nodes_1 <= dv.honest_nodes_states.Keys
        && h_nodes_2 <= dv.honest_nodes_states.Keys
        && |h_nodes_1| >= quorum(|dv.all_nodes|) - |dv.adversary.nodes|
        && |h_nodes_2| >= quorum(|dv.all_nodes|) - |dv.adversary.nodes|
        ==>
        exists hn ::
            && hn in dv.honest_nodes_states.Keys
            && hn in h_nodes_1
            && hn in h_nodes_2
    }

    predicate inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_body(
        dv: DVState,
        hn: BLSPubkey,
        slot: Slot, 
        vp: AttestationData -> bool, 
        db: set<SlashingDBAttestation>
    )
    {
        forall att_share: AttestationShare | 
            && att_share in dv.att_network.allMessagesSent
            && is_honest_node(dv, hn)
            && var dvc := dv.honest_nodes_states[hn];
            && var rs_pubkey := dvc.rs.pubkey;
            && pred_verify_owner_of_attestation_share_with_bls_signature(rs_pubkey, att_share)
            && att_share.data.slot < slot
            ::
            && var att_data := att_share.data;
            && var slashing_db_attestation := SlashingDBAttestation(
                                            source_epoch := att_data.source.epoch,
                                            target_epoch := att_data.target.epoch,
                                            signing_root := Some(hash_tree_root(att_data)));
            && slashing_db_attestation in db
    }

    predicate inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv: DVState)
    {
        forall hn: BLSPubkey, slot: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation> | 
            && is_honest_node(dv, hn) 
            && var dvc := dv.honest_nodes_states[hn];
            && slot in dvc.attestation_consensus_engine_state.att_slashing_db_hist
            && vp in dvc.attestation_consensus_engine_state.att_slashing_db_hist[slot]
            && db in dvc.attestation_consensus_engine_state.att_slashing_db_hist[slot][vp]
            :: 
            inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_body(
                dv,
                hn,
                slot,
                vp,
                db)
    }

    predicate inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_body_dvc(
        allMessagesSent: set<AttestationShare>,
        rs_pubkey: BLSPubkey,
        slot: Slot, 
        vp: AttestationData -> bool, 
        db: set<SlashingDBAttestation>
    )
    {
        forall att_share: AttestationShare | 
            && att_share in allMessagesSent
            && pred_verify_owner_of_attestation_share_with_bls_signature(rs_pubkey, att_share)
            && att_share.data.slot < slot
            ::
            && var att_data := att_share.data;
            && var slashing_db_attestation := SlashingDBAttestation(
                                            source_epoch := att_data.source.epoch,
                                            target_epoch := att_data.target.epoch,
                                            signing_root := Some(hash_tree_root(att_data)));
            && slashing_db_attestation in db
    }

    predicate inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_dvc(
        allMessagesSent: set<AttestationShare>,
        dvc: DVCState        
    )
    {
        forall slot: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation> | 
            && slot in dvc.attestation_consensus_engine_state.att_slashing_db_hist
            && vp in dvc.attestation_consensus_engine_state.att_slashing_db_hist[slot]
            && db in dvc.attestation_consensus_engine_state.att_slashing_db_hist[slot][vp]
            :: 
            inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_body_dvc(
                allMessagesSent,
                dvc.rs.pubkey,
                slot,
                vp,
                db
            )
    }

    predicate inv_unchanged_dvc_rs_pubkey(dv: DVState)
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            && var dvc: DVCState := dv.honest_nodes_states[hn];
            && dvc.rs.pubkey == hn
    }

    predicate inv_honest_nodes_are_not_owner_of_att_shares_from_adversary_body(
        dv: DVState, 
        att_share: AttestationShare
    )
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) :: 
            !pred_verify_owner_of_attestation_share_with_bls_signature(hn, att_share)
    }

    predicate inv_honest_nodes_are_not_owner_of_att_shares_from_adversary(dv: DVState)
    {
        forall byz_node: BLSPubkey, att_share: AttestationShare | 
            && byz_node in dv.adversary.nodes 
            && att_share in dv.att_network.allMessagesSent
            && pred_verify_owner_of_attestation_share_with_bls_signature(byz_node, att_share)
            ::
            inv_honest_nodes_are_not_owner_of_att_shares_from_adversary_body(dv, att_share)
    }
}