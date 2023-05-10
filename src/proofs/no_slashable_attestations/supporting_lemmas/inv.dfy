include "../../../common/commons.dfy"
include "../common/dvc_attestation_creation_instrumented.dfy"
include "../../../specs/consensus/consensus.dfy"
include "../../../specs/network/network.dfy"
include "../../../specs/dv/dv_attestation_creation.dfy"
include "../../common/helper_sets_lemmas.dfy"
include "../../bn_axioms.dfy"
include "../../rs_axioms.dfy"

module Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened Att_DVC_Spec
    import opened Att_DV
    import opened Helper_Sets_Lemmas
    import opened BN_Axioms
    import opened RS_Axioms


    predicate is_an_honest_node(s: Att_DVState, n: BLSPubkey)
    {
        n in s.honest_nodes_states.Keys
    }

    predicate inv_rcvd_attestation_shares_are_sent_messages_body(
        dv: Att_DVState,
        dvc: Att_DVCState
    )
    {
        && var rcvd_attestation_shares := dvc.rcvd_attestation_shares;
        && forall i, j |
            && i in rcvd_attestation_shares.Keys 
            && j in rcvd_attestation_shares[i].Keys
            ::
            rcvd_attestation_shares[i][j] <= dv.att_network.allMessagesSent
    }

    predicate inv_rcvd_attestation_shares_are_sent_messages(
        dv: Att_DVState    
    )
    {
        forall n | n in dv.honest_nodes_states.Keys ::
            inv_rcvd_attestation_shares_are_sent_messages_body(dv, dv.honest_nodes_states[n])
    }  

    predicate inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_body(
        dv: Att_DVState,
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

    predicate inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(dv: Att_DVState)
    {
        forall a |
            && a in dv.all_attestations_created
            && is_valid_attestation(a, dv.dv_pubkey)
            ::
            exists hn, att_share: AttestationShare :: inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_body(dv, hn, att_share, a)
    }

    predicate inv_data_of_att_shares_are_decided_values(dv: Att_DVState)
    {
        forall hn, att_share |
                && hn in dv.honest_nodes_states.Keys 
                && att_share in dv.att_network.allMessagesSent
                && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));                
                && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
                && verify_bls_signature(attestation_signing_root, att_share.signature, hn)
            ::
                inv_data_of_att_shares_are_decided_values_body(dv, att_share)
    }  

    predicate inv_data_of_att_shares_are_decided_values_body(dv: Att_DVState, att_share: AttestationShare)
    {
        && dv.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent()
        && dv.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data
    }  

    predicate inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(dv: Att_DVState)
    {
        forall cid |
            && cid in dv.consensus_on_attestation_data.Keys
            && dv.consensus_on_attestation_data[cid].decided_value.isPresent()
            ::
            is_a_valid_decided_value(dv.consensus_on_attestation_data[cid])
    }  

    predicate inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(dv: Att_DVState)
    {
        forall cid |
            && cid in dv.consensus_on_attestation_data.Keys
            && dv.consensus_on_attestation_data[cid].decided_value.isPresent()
            ::
            dv.consensus_on_attestation_data[cid].decided_value.safe_get().slot == cid
    }     

    predicate inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_body(
        s: Slot,
        attestation_duty: AttestationDuty,
        attestation_slashing_db: set<SlashingDBAttestation>,
        vp: AttestationData -> bool
    )
    {
        && attestation_duty.slot == s
        && (vp == (ad: AttestationData) => ci_decision_is_valid_attestation_data(attestation_slashing_db, ad, attestation_duty))
    }

    predicate inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(dv: Att_DVState)
    {
        forall hn, s: Slot, vp |
            && hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
            && vp in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions[hn]
            ::
            exists attestation_duty, attestation_slashing_db ::
                inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_body(s, attestation_duty, attestation_slashing_db, vp)
    }    

    predicate inv_existing_slashing_db_for_given_att_duty_and_vp(
        cid: Slot,
        attestation_duty: AttestationDuty,
        vp: AttestationData -> bool
    )
    {
        exists attestation_slashing_db ::
            inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_body(cid, attestation_duty, attestation_slashing_db, vp)        
    }      
    
    predicate inv_every_active_consensus_instance_has_a_corresponding_att_duty_and_a_validity_predicate(
        dv: Att_DVState,
        n: BLSPubkey,
        cid: Slot
    )
    requires n in dv.honest_nodes_states.Keys 
    requires cid in dv.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
    {
        &&  var dvc := dv.honest_nodes_states[n];
        &&  var acvc := dvc.attestation_consensus_engine_state.active_attestation_consensus_instances[cid];
        &&  inv_existing_slashing_db_for_given_att_duty_and_vp(
                cid, 
                acvc.attestation_duty, 
                acvc.validityPredicate
            ) 
    }

    predicate inv_exist_an_att_duty_and_a_validity_predicate_for_an_active_consensus_instance_at_slot_cid(
        dvc: Att_DVCState,
        cid: Slot
    )
    requires cid in dvc.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
    {
        &&  var acvc := dvc.attestation_consensus_engine_state.active_attestation_consensus_instances[cid];
        &&  inv_existing_slashing_db_for_given_att_duty_and_vp(
                cid, 
                acvc.attestation_duty, 
                acvc.validityPredicate
            ) 
    }     

    predicate inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate(
        dvc: Att_DVCState
    )
    {
        forall cid | 
            && cid in dvc.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
            ::
            inv_exist_an_att_duty_and_a_validity_predicate_for_an_active_consensus_instance_at_slot_cid(dvc, cid)        
    }    

    predicate inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(
        dv: Att_DVState
    )
    {
        forall n, cid | 
            && n in dv.honest_nodes_states.Keys
            && cid in dv.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
            ::
            inv_every_active_consensus_instance_has_a_corresponding_att_duty_and_a_validity_predicate(dv, n, cid)
    }

    // predicate inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_dbi(dv: Att_DVState)    
    // {
    //     forall hn, s1: Slot, s2: Slot, vp, db2 |
    //         && hn in dv.honest_nodes_states.Keys
    //         && var hn_state := dv.honest_nodes_states[hn];
    //         && s2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys            
    //         && s1 < s2
    //         && hn in dv.consensus_on_attestation_data[s1].honest_nodes_validity_functions.Keys
    //         && hn in dv.consensus_on_attestation_data[s2].honest_nodes_validity_functions.Keys
    //         && vp in dv.consensus_on_attestation_data[s2].honest_nodes_validity_functions[hn]        
    //         && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys   
    //         && db2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp]          
    //         && dv.consensus_on_attestation_data[s1].decided_value.isPresent()
    //         ::                
    //         && var hn_state := dv.honest_nodes_states[hn];
    //         && dv.consensus_on_attestation_data[s1].decided_value.isPresent()
    //         && var decided_att_data := dv.consensus_on_attestation_data[s1].decided_value.safe_get();
    //         && var sdba := construct_SlashingDBAttestation_from_att_data(decided_att_data);
    //         && sdba in db2
    // }    

    predicate inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist(dv: Att_DVState)    
    {
        forall hn | hn in dv.honest_nodes_states.Keys          
            ::
            inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn],
                dv.index_next_attestation_duty_to_be_served
            )                    
    }       

    predicate inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(
        dv: Att_DVState, 
        n: BLSPubkey,
        n_state: Att_DVCState,
        index_next_attestation_duty_to_be_served: nat
    )
    {
        forall slot  |
            && slot in n_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
            ::
            exists i: Slot :: 
                && i < index_next_attestation_duty_to_be_served
                && var an := dv.sequence_attestation_duties_to_be_served[i];
                && an.attestation_duty.slot == slot 
                && an.node == n
    }   

    function get_upperlimit_active_instances(
        n_state: Att_DVCState
    ): nat 
    {
        if n_state.latest_attestation_duty.isPresent() then
            n_state.latest_attestation_duty.safe_get().slot + 1
        else
            0
    }                

    predicate inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body(
        dvc: Att_DVCState       
    )
    {
        forall slot: Slot |
            && slot in dvc.attestation_consensus_engine_state.att_slashing_db_hist.Keys
            ::
            slot < get_upperlimit_active_instances(dvc)
    }     

    predicate inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty(
        dv: Att_DVState        
    )
    {
        forall hn: BLSPubkey | is_an_honest_node(dv, hn) ::
                inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_att_duty_body(dv.honest_nodes_states[hn])        
    }     
    
    predicate inv_latest_att_duty_is_from_dv_seq_of_att_duties(dv: Att_DVState)    
    {
        forall hn | hn in dv.honest_nodes_states.Keys ::
            inv_latest_att_duty_is_from_dv_seq_of_att_duties_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn],
                dv.index_next_attestation_duty_to_be_served
            )                    
    }               

    predicate inv_latest_att_duty_is_from_dv_seq_of_att_duties_body(
        dv: Att_DVState, 
        n: BLSPubkey,
        n_state: Att_DVCState,
        index_next_attestation_duty_to_be_served: nat
    )
    {
        n_state.latest_attestation_duty.isPresent() 
        ==>
        exists i: Slot :: 
            && i < index_next_attestation_duty_to_be_served
            && var an := dv.sequence_attestation_duties_to_be_served[i];
            && an.attestation_duty == n_state.latest_attestation_duty.safe_get()
            && an.node == n
    }     

    predicate pred_exists_an_att_duty_from_dv_seq_of_att_duties_for_a_given_att_duty(  
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

    predicate inv_available_latest_att_duty_is_from_dv_seq_of_att_duties(  
        n: BLSPubkey,
        n_state: Att_DVCState,
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

    // function get_upperlimit_decided_instances(
    //     n_state: Att_DVCState
    // ): nat 
    // {
    //     if n_state.latest_attestation_duty.isPresent() then
    //         if n_state.current_attestation_duty.isPresent() then 
    //             n_state.latest_attestation_duty.safe_get().slot
    //         else
    //             n_state.latest_attestation_duty.safe_get().slot + 1
    //     else
    //         0
    // }

    predicate inv_future_decisions_known_by_dvc_are_decisions_of_quorums(dv: Att_DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_future_decisions_known_by_dvc_are_decisions_of_quorums_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn]
            )                    
    }       

    predicate inv_future_decisions_known_by_dvc_are_decisions_of_quorums_body(
        dv: Att_DVState, 
        n: BLSPubkey,
        n_state: Att_DVCState
    )
    {
        forall slot |
            && slot in n_state.future_att_consensus_instances_already_decided.Keys
            ::
            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
            && n_state.future_att_consensus_instances_already_decided[slot] == dv.consensus_on_attestation_data[slot].decided_value.safe_get()
    }  

    predicate inv_slots_in_future_decided_data_are_correct(dv: Att_DVState)    
    {
        forall hn | hn in dv.honest_nodes_states.Keys          
            ::
            inv_slots_in_future_decided_data_are_correct_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn]
            )                    
    }              

    predicate inv_slots_in_future_decided_data_are_correct_body(
        dv: Att_DVState, 
        n: BLSPubkey,
        n_state: Att_DVCState
    )
    {
        forall slot | slot in n_state.future_att_consensus_instances_already_decided.Keys
            ::
            n_state.future_att_consensus_instances_already_decided[slot].slot == slot
    }       

    predicate inv_the_domain_of_active_attestation_consensus_instances_is_a_subset_of_att_slashing_db_hist(dv: Att_DVState)    
    {
        forall hn |hn in dv.honest_nodes_states.Keys  ::
            inv_the_domain_of_active_attestation_consensus_instances_is_a_subset_of_att_slashing_db_hist_body(
                dv.honest_nodes_states[hn]
            )                    
    }       

    predicate inv_the_domain_of_active_attestation_consensus_instances_is_a_subset_of_att_slashing_db_hist_body
    (
        n_state: Att_DVCState
    )
    {
        n_state.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys <= n_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    }

    predicate inv_active_attestation_consensus_instances_predicate_is_in_att_slashing_db_hist(dv: Att_DVState)    
    {
        forall hn, cid | hn in dv.honest_nodes_states.Keys ::
            inv_validitty_predicates_of_active_attestation_consensus_instances_are_tracked_in_att_slashing_db_hist_body(dv.honest_nodes_states[hn], cid)
             
    }       

    predicate inv_validitty_predicates_of_active_attestation_consensus_instances_are_tracked_in_att_slashing_db_hist_body
    (
        n_state: Att_DVCState,
        cid: Slot
    )
    {
        cid in n_state.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
        ==>
        (
            && cid in n_state.attestation_consensus_engine_state.att_slashing_db_hist
            && n_state.attestation_consensus_engine_state.active_attestation_consensus_instances[cid].validityPredicate in n_state.attestation_consensus_engine_state.att_slashing_db_hist[cid] 
        )
    }    

    predicate inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(
        dvc: Att_DVCState,
        hn: BLSPubkey,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    {
       forall att_duty |
            att_duty in dvc.all_rcvd_duties
            ::
            inv_exists_an_att_duty_in_dv_seq_of_att_duties_for_a_given_att_duty(                
                att_duty, 
                hn, 
                sequence_attestation_duties_to_be_served,
                index_next_attestation_duty_to_be_served)
    }

    predicate inv_exists_an_att_duty_in_dv_seq_of_att_duties_for_a_given_att_duty(        
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

    predicate inv_rcvd_att_duties_are_from_dv_seq_of_att_duties(dv: Att_DVState)
    {
        forall hn: BLSPubkey | 
            is_an_honest_node(dv, hn) 
            ::
            && var hn_state := dv.honest_nodes_states[hn];
            && inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(                    
                    hn_state, 
                    hn, 
                    dv.sequence_attestation_duties_to_be_served,
                    dv.index_next_attestation_duty_to_be_served)
    }  

    // predicate has_all_slashing_db_attestations_before_slot_s(
    //     db: set<SlashingDBAttestation>,
    //     S: set<SlashingDBAttestation>,
    //     s: Slot
    // )
    // requires (forall r: SlashingDBAttestation :: 
    //                 r in db ==> (exists data: AttestationData :: r.signing_root == Some(hash_tree_root(data))))
    // {
    //     && S <= db
    //     && ( forall r | r in db && r !in S :: get_slot_from_slashing_db_attestation(r) >= s )
    //     && ( forall r | r in S :: get_slot_from_slashing_db_attestation(r) < s )
    // }

    predicate inv_sent_validity_predicates_are_only_for_slots_stored_in_att_slashing_db_hist(dv: Att_DVState)
    {
        forall hn: BLSPubkey, s: Slot | is_an_honest_node(dv, hn) ::
            && var hn_state := dv.honest_nodes_states[hn];
            && ( hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
                 ==> 
                 s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys)
    }

    predicate inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body(
        dv: Att_DVState, 
        hn: BLSPubkey,
        hn_state: Att_DVCState,
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
    
    predicate inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv: Att_DVState)
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

    // predicate honest_nodes_with_validityPredicate(consa: ConsensusInstance<AttestationData>,  h_nodes_a: set<BLSPubkey>)
    // requires h_nodes_a <= consa.honest_nodes_validity_functions.Keys  
    // requires |h_nodes_a| >= quorum(|consa.all_nodes|) 
    //                                     - (|consa.all_nodes| - |consa.honest_nodes_status.Keys|)
    // requires consa.decided_value.isPresent()
    // {
    //     forall n | n in h_nodes_a 
    //         :: exists vp: AttestationData -> bool | vp in consa.honest_nodes_validity_functions[n] 
    //                 :: vp(consa.decided_value.safe_get())
    // }
    
    // predicate inv_exists_honest_node_that_contributed_to_decisions_of_consensus_instances(
    //     dv: Att_DVState, 
    //     a: Attestation, a': Attestation, 
    //     m: BLSPubkey,
    //     consa: ConsensusInstance<AttestationData>, consa': ConsensusInstance<AttestationData>,
    //     h_nodes_a: set<BLSPubkey>, h_nodes_a': set<BLSPubkey>)
    // {
    //     && is_an_honest_node(dv, m)                
    //     && consa == dv.consensus_on_attestation_data[a.data.slot]
    //     && consa' == dv.consensus_on_attestation_data[a'.data.slot]
    //     && m in consa.honest_nodes_validity_functions.Keys
    //     && m in h_nodes_a
    //     && m in consa'.honest_nodes_validity_functions.Keys                
    //     && m in h_nodes_a'
    //     && consa'.honest_nodes_validity_functions[m] != {}
    //     && is_a_valid_decided_value_according_to_set_of_nodes(consa, h_nodes_a) 
    //     && is_a_valid_decided_value_according_to_set_of_nodes(consa', h_nodes_a') 
    // }

    predicate inv_unique_rcvd_att_duty_per_slot(dv: Att_DVState)
    {
        forall hn: BLSPubkey | 
            is_an_honest_node(dv, hn) 
            ::
            inv_unique_rcvd_att_duty_per_slot_body(dv.honest_nodes_states[hn])
    }

    predicate inv_unique_rcvd_att_duty_per_slot_body(dvc: Att_DVCState)
    {
        forall d1: AttestationDuty, d2: AttestationDuty | 
            && d1 in dvc.all_rcvd_duties
            && d2 in dvc.all_rcvd_duties
            && d1.slot == d2.slot
            ::
            d1 == d2
    }

    predicate inv_every_sent_validity_predicate_is_based_on_an_existing_slashing_db_and_a_rcvd_att_duty_body(
        dv: Att_DVState, 
        hn: BLSPubkey, 
        s: Slot, 
        db: set<SlashingDBAttestation>, 
        duty: AttestationDuty, 
        vp: AttestationData -> bool)
    requires && is_an_honest_node(dv, hn)
             && var hn_state := dv.honest_nodes_states[hn];
             && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
             && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s].Keys
    {
        && var hn_state := dv.honest_nodes_states[hn];
        && duty.slot == s
        && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
        && vp == (ad: AttestationData) => ci_decision_is_valid_attestation_data(db, ad, duty)
    }

    predicate inv_every_sent_validity_predicate_is_based_on_an_existing_slashing_db_and_a_rcvd_att_duty(dv: Att_DVState)
    {
        forall hn: BLSPubkey, s: Slot, vp: AttestationData -> bool | 
            && is_an_honest_node(dv, hn)
            && var hn_state := dv.honest_nodes_states[hn];
            && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
            && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s].Keys
            ::
            exists duty, db ::
                && var hn_state := dv.honest_nodes_states[hn];
                && inv_every_sent_validity_predicate_is_based_on_an_existing_slashing_db_and_a_rcvd_att_duty_body(dv, hn, s, db, duty, vp)
    }

    predicate inv_every_decided_data_has_an_honest_witness_body<D(!new, 0)>(ci: ConsensusInstance) 
    {
        ci.decided_value.isPresent()
        ==> 
        is_a_valid_decided_value(ci)
    }
    
    predicate inv_every_decided_data_has_an_honest_witness(dv: Att_DVState)
    {
        forall s: Slot ::
            && var ci := dv.consensus_on_attestation_data[s];
            && inv_every_decided_data_has_an_honest_witness_body(ci)            
    }

    predicate same_honest_nodes_in_dv_and_ci(dv: Att_DVState)
    {
        forall s: Slot ::
            && var ci := dv.consensus_on_attestation_data[s];            
            && dv.all_nodes == ci.all_nodes
            && dv.honest_nodes_states.Keys == ci.honest_nodes_status.Keys
    }

    predicate inv_all_honest_nodes_is_a_quorum(dv: Att_DVState)
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

    predicate inv_unchanged_paras_of_consensus_instances(dv: Att_DVState)
    {
        forall ci | ci in dv.consensus_on_attestation_data.Values
            :: && ci.all_nodes == dv.all_nodes
               && ci.honest_nodes_status.Keys == dv.honest_nodes_states.Keys  
               && ci.honest_nodes_status.Keys <= ci.all_nodes
               && ci.honest_nodes_validity_functions.Keys <= ci.honest_nodes_status.Keys
               && |ci.all_nodes - ci.honest_nodes_status.Keys| <= f(|ci.all_nodes|)
    }

    predicate inv_only_dv_construct_signed_attestation_signature(dv: Att_DVState)
    {
        && construct_signed_attestation_signature_assumptions(dv)                
        && forall n | n in dv.honest_nodes_states.Keys :: 
                && var nodes := dv.honest_nodes_states[n];
                && nodes.construct_signed_attestation_signature == dv.construct_signed_attestation_signature
                && nodes.dv_pubkey == dv.dv_pubkey       
                && nodes.peers == dv.all_nodes
    }

    predicate inv_current_att_duty_is_rcvd_duty_body(dvc: Att_DVCState)
    {
        dvc.current_attestation_duty.isPresent()
        ==> 
        dvc.current_attestation_duty.safe_get() in dvc.all_rcvd_duties
    }

    predicate inv_current_att_duty_is_rcvd_duty(dv: Att_DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_current_att_duty_is_rcvd_duty_body(dvc)
    }

    predicate inv_latest_att_duty_is_rcvd_duty_body(dvc: Att_DVCState)
    {
        dvc.latest_attestation_duty.isPresent()
        ==> 
        dvc.latest_attestation_duty.safe_get() in dvc.all_rcvd_duties
    }

    predicate inv_latest_att_duty_is_rcvd_duty(dv: Att_DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_latest_att_duty_is_rcvd_duty_body(dvc)
    }

    predicate inv_none_latest_att_duty_implies_none_current_att_duty_body(dvc: Att_DVCState)
    {
        !dvc.latest_attestation_duty.isPresent()
        ==> 
        !dvc.current_attestation_duty.isPresent()
    }

    predicate inv_none_latest_att_duty_implies_none_current_att_duty(dv: Att_DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_none_latest_att_duty_implies_none_current_att_duty_body(dvc)
    }
  
    predicate inv_current_att_duty_is_either_none_or_latest_att_duty_body(dvc: Att_DVCState)
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

    predicate inv_current_att_duty_is_either_none_or_latest_att_duty(dv: Att_DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_current_att_duty_is_either_none_or_latest_att_duty_body(dvc)
    }

    predicate inv_available_current_att_duty_is_latest_att_duty_body(dvc: Att_DVCState)
    {
        dvc.current_attestation_duty.isPresent()
        ==> 
        ( && dvc.latest_attestation_duty.isPresent()
          && dvc.current_attestation_duty.safe_get()
                                == dvc.latest_attestation_duty.safe_get()                   
        )
    }

    predicate inv_available_current_att_duty_is_latest_att_duty(dv: Att_DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_available_current_att_duty_is_latest_att_duty_body(dvc)
    }

    predicate inv_an_att_duty_in_the_next_delivery_is_not_lower_than_current_att_duty_body(dvc: Att_DVCState, next_duty: AttestationDuty)
    {
        dvc.current_attestation_duty.isPresent()
        ==> 
        dvc.current_attestation_duty.safe_get().slot <= next_duty.slot        
    }

    predicate inv_an_att_duty_in_the_next_delivery_is_not_lower_than_current_att_duty(dv: Att_DVState)
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
            && inv_an_att_duty_in_the_next_delivery_is_not_lower_than_current_att_duty_body(dvc, next_duty)
    }

    predicate inv_an_att_duty_in_the_next_delivery_is_not_lower_than_latest_att_duty_body(dvc: Att_DVCState, next_duty: AttestationDuty)
    {
        dvc.latest_attestation_duty.isPresent()
        ==> 
        dvc.latest_attestation_duty.safe_get().slot <= next_duty.slot        
    }

    predicate inv_an_att_duty_in_the_next_delivery_is_not_lower_than_latest_att_duty(dv: Att_DVState)
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
            && inv_an_att_duty_in_the_next_delivery_is_not_lower_than_latest_att_duty_body(dvc, next_duty)
    }

    predicate inv_an_att_duty_in_the_next_delivery_is_not_lower_than_rcvd_att_duties_body(dvc: Att_DVCState, next_duty: AttestationDuty)
    {
       forall rcvd_duty: AttestationDuty | rcvd_duty in dvc.all_rcvd_duties ::
            rcvd_duty.slot <= next_duty.slot        
    }

    predicate inv_an_att_duty_in_the_next_delivery_is_not_lower_than_rcvd_att_duties(dv: Att_DVState)
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
            && inv_an_att_duty_in_the_next_delivery_is_not_lower_than_rcvd_att_duties_body(dvc, next_duty)
    }

    predicate inv_in_transit_messages_are_in_allMessagesSent(
        dv: Att_DVState
    )
    {
         forall m | m in dv.att_network.messagesInTransit ::
                m.message in dv.att_network.allMessagesSent       
    }

    predicate inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent_single_node(
        dv: Att_DVState,
        n: BLSPubkey
    )
    requires n in dv.honest_nodes_states.Keys 
    {
        dv.honest_nodes_states[n].attestation_shares_to_broadcast.Values <= dv.att_network.allMessagesSent
    }

    predicate inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(
        dv: Att_DVState
    )
    {
        forall n | n in dv.honest_nodes_states.Keys ::
            inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent_single_node(dv, n)
    }    

    predicate inv_no_duplicated_att_duties(dv: Att_DVState)
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

    predicate pred_unchanged_dvn_seq_of_att_duties(dv: Att_DVState, dv': Att_DVState)
    {
        dv.sequence_attestation_duties_to_be_served
                == dv'.sequence_attestation_duties_to_be_served
    }

    predicate inv_every_att_duty_before_dvn_att_index_was_delivered_body(dvc: Att_DVCState, duty: AttestationDuty)
    {
        duty in dvc.all_rcvd_duties
    }

    predicate inv_every_att_duty_before_dvn_att_index_was_delivered(dv: Att_DVState)
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

    predicate inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(dvc: Att_DVCState)
    {
        !dvc.latest_attestation_duty.isPresent()
        ==> 
        dvc.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys == {}
    }

    predicate inv_no_active_consensus_instances_before_the_first_att_duty_was_received(dv: Att_DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(dvc)
    }
    
    predicate inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(dvc: Att_DVCState)
    {
        dvc.latest_attestation_duty.isPresent()
        ==> ( forall k: Slot | k in dvc.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys 
                ::
                k <= dvc.latest_attestation_duty.safe_get().slot
            )
    }

    predicate inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty(dv: Att_DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(dvc)
    }

    predicate inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(dvc: Att_DVCState)
    {
        forall k: Slot | k in dvc.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys ::
            exists rcvd_duty: AttestationDuty :: 
                && rcvd_duty in dvc.all_rcvd_duties
                && rcvd_duty.slot == k
    }

    predicate inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance(dv: Att_DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(dvc)
    }

    predicate inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(dvc: Att_DVCState)
    {
        forall k: Slot | k in dvc.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys 
            ::
            && dvc.attestation_consensus_engine_state.active_attestation_consensus_instances[k].attestation_duty in dvc.all_rcvd_duties                
            && dvc.attestation_consensus_engine_state.active_attestation_consensus_instances[k].attestation_duty.slot == k
    }

    predicate inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k(dv: Att_DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(dvc)
    }

    predicate inv_active_consensus_instances_imply_the_delivery_of_att_duties_body(hn_state: Att_DVCState, s: Slot)
    requires s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    {
        exists duty: AttestationDuty :: 
                    && duty in hn_state.all_rcvd_duties
                    && duty.slot == s
    }


    predicate inv_active_consensus_instances_imply_the_delivery_of_att_duties(dv: Att_DVState)
    {
        forall hn: BLSPubkey, s: Slot ::
            ( && is_an_honest_node(dv, hn) 
              && var hn_state := dv.honest_nodes_states[hn];
              && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
            )
            ==>
            inv_active_consensus_instances_imply_the_delivery_of_att_duties_body(dv.honest_nodes_states[hn], s)                
    }

    predicate inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(hn_state: Att_DVCState)    
    {
        forall k: Slot | k in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys ::
            exists duty: AttestationDuty :: 
                    && duty in hn_state.all_rcvd_duties
                    && duty.slot == k
    }

    predicate inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties(dv: Att_DVState)
    {
        forall hn: BLSPubkey | is_an_honest_node(dv, hn) ::
            && var hn_state := dv.honest_nodes_states[hn];            
            && inv_att_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(hn_state)       
    }

    predicate inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body_ces(ces: ConsensusEngineState)
    {
        forall s: Slot, vp: AttestationData -> bool |
                ( && s in ces.att_slashing_db_hist.Keys
                  && vp in ces.att_slashing_db_hist[s].Keys
                )
                :: 
                ( exists db: set<SlashingDBAttestation>, duty: AttestationDuty ::
                        && duty.slot == s
                        && db in ces.att_slashing_db_hist[s][vp]
                        && vp == (ad: AttestationData) => ci_decision_is_valid_attestation_data(db, ad, duty)
                )
    }

    predicate inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body(hn_state: Att_DVCState)
    {
        forall s: Slot, vp: AttestationData -> bool |
                ( && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                  && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s].Keys
                )
                :: 
                ( exists db: set<SlashingDBAttestation>, duty: AttestationDuty ::
                        && duty.slot == s
                        && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
                        && vp == (ad: AttestationData) => ci_decision_is_valid_attestation_data(db, ad, duty)
                )
    }

    predicate inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate(dv: Att_DVState)
    {
        forall hn: BLSPubkey | is_an_honest_node(dv, hn) ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_exist_a_db_in_att_slashing_db_hist_and_an_att_duty_for_every_validity_predicate_body(dvc)
    }

    predicate inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(hn_state: Att_DVCState)
    {
        forall k: Slot |
            k in hn_state.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys ::
                && var ci := hn_state.attestation_consensus_engine_state.active_attestation_consensus_instances[k];
                && var vp: AttestationData -> bool := ci.validityPredicate;
                && k in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
                && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[k].Keys             
    }

    predicate inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k(dv: Att_DVState)
    {
        forall hn: BLSPubkey | is_an_honest_node(dv, hn) ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(dvc)
    }

    predicate inv_monotonic_att_slashing_db_body(dvc: Att_DVCState, dvc': Att_DVCState)
    {
        dvc.attestation_slashing_db <= dvc'.attestation_slashing_db
    }

    predicate inv_monotonic_att_slashing_db(dv: Att_DVState, event: Att_DV.AttestationEvent, dv': Att_DVState)    
    {
        forall hn: BLSPubkey | is_an_honest_node(dv, hn) ::
            && hn in dv'.honest_nodes_states.Keys
            && var dvc := dv.honest_nodes_states[hn];
            && var dvc' := dv'.honest_nodes_states[hn];
            && inv_monotonic_att_slashing_db_body(dvc, dvc')
    }

    predicate inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body_ces(ces: ConsensusEngineState, attestation_slashing_db: set<SlashingDBAttestation>)
    {
        forall s: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation> |
                ( && s in ces.att_slashing_db_hist.Keys
                  && vp in ces.att_slashing_db_hist[s].Keys
                  && db in ces.att_slashing_db_hist[s][vp]
                )
                :: 
                db <= attestation_slashing_db
    }

    predicate inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(hn_state: Att_DVCState)
    {
        forall s: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation> |
                ( && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                  && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s].Keys
                  && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
                )
                :: 
                db <= hn_state.attestation_slashing_db
    }

    predicate inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db(dv: Att_DVState)
    {
        forall hn: BLSPubkey | is_an_honest_node(dv, hn) ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_every_db_in_att_slashing_db_hist_is_a_subset_of_att_slashing_db_body(dvc)
    }

    predicate inv_monotonic_att_slashing_db_hist_body(dvc: Att_DVCState, dvc': Att_DVCState)
    {        
        dvc.attestation_consensus_engine_state.att_slashing_db_hist.Keys
        <= 
        dvc'.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    }

    predicate inv_monotonic_att_slashing_db_hist(dv: Att_DVState, event: Att_DV.AttestationEvent, dv': Att_DVState)    
    {
        forall hn: BLSPubkey | is_an_honest_node(dv, hn) ::
            && hn in dv'.honest_nodes_states.Keys
            && var dvc := dv.honest_nodes_states[hn];
            && var dvc' := dv'.honest_nodes_states[hn];
            && inv_monotonic_att_slashing_db_hist_body(dvc, dvc')
    }

    predicate prop_monotonic_set_of_in_transit_messages(dv: Att_DVState, dv': Att_DVState)
    {
        && dv.att_network.allMessagesSent <= dv'.att_network.allMessagesSent
    }
     
   
    predicate inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body(dvc: Att_DVCState)
    {
        dvc.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys 
        <= 
        dvc.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    } 

    predicate inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist(dv: Att_DVState)
    {
        forall hn | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_active_att_consensus_instances_are_tracked_in_att_slashing_db_hist_body(dvc)
    } 

    predicate inv_construct_signed_attestation_signature_assumptions_helper(dv: Att_DVState)
    {
        construct_signed_attestation_signature_assumptions_helper(
            dv.construct_signed_attestation_signature,
            dv.dv_pubkey,
            dv.all_nodes)
    }

    predicate inv_all_in_transit_messages_were_sent_body<M>(e: Network<M>)
    {
         forall m | m in e.messagesInTransit ::
                m.message in e.allMessagesSent       
    } 
     
    predicate inv_all_in_transit_messages_were_sent(dv: Att_DVState)
    {
         forall m | m in dv.att_network.messagesInTransit ::
                m.message in dv.att_network.allMessagesSent       
    } 

    predicate inv_rcvd_att_shares_are_from_sent_messages_body(
        dv: Att_DVState,
        dvc: Att_DVCState
    )
    {
        var rcvd_attestation_shares := dvc.rcvd_attestation_shares;

        forall i, j |
            && i in rcvd_attestation_shares.Keys 
            && j in rcvd_attestation_shares[i].Keys
            ::
            rcvd_attestation_shares[i][j] <= dv.att_network.allMessagesSent
    }    

    predicate inv_rcvd_att_shares_are_from_sent_messages(
        dv: Att_DVState    
    )
    {
        forall n | n in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[n];
            && inv_rcvd_att_shares_are_from_sent_messages_body(dv, dvc)
    } 


    predicate inv_attestation_shares_to_broadcast_are_sent_messages_body(
        dv: Att_DVState,
        dvc: Att_DVCState
    )    
    {
        dvc.attestation_shares_to_broadcast.Values <= dv.att_network.allMessagesSent
    }

    predicate inv_attestation_shares_to_broadcast_are_sent_messages(
        dv: Att_DVState
    )
    {
        forall n | n in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[n];
            && inv_attestation_shares_to_broadcast_are_sent_messages_body(dv, dvc)
    }

    // predicate inv39(
    //     dv: Att_DVState,        
    //     dv': Att_DVState
    // )       
    // {
    //     dv.att_network.allMessagesSent <= dv'.att_network.allMessagesSent
    // }
    
    predicate inv_slots_for_sent_validity_predicates_are_stored_in_att_slashing_db_hist_body(
        dv: Att_DVState, 
        hn: BLSPubkey,
        hn_state: Att_DVCState,
        s: Slot
    )
    {
        hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
        ==> s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    }

    predicate inv_slots_for_sent_validity_predicates_are_stored_in_att_slashing_db_hist(dv: Att_DVState)
    {
        forall hn: BLSPubkey, s: Slot | hn in dv.honest_nodes_states.Keys :: 
            inv_slots_for_sent_validity_predicates_are_stored_in_att_slashing_db_hist_body(dv, hn, dv.honest_nodes_states[hn], s)        
    } 

    predicate inv_every_consensus_instance_isConditionForSafetyTrue(dv: Att_DVState)
    {
        forall slot: Slot | slot in dv.consensus_on_attestation_data.Keys  ::
                    isConditionForSafetyTrue(dv.consensus_on_attestation_data[slot])                    
    }

    predicate pred_last_att_duty_is_delivering_to_given_honest_node(
        attestation_duty: AttestationDuty,
        dv: Att_DVState,
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

    predicate inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_body(dvc: Att_DVCState)
    {
        !dvc.latest_attestation_duty.isPresent()
        <==> 
        dvc.all_rcvd_duties == {}
    }

    predicate inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties(dv: Att_DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_body(dv.honest_nodes_states[hn])
    }

    predicate inv_no_rcvd_att_duties_are_higher_than_latest_att_duty_body(dvc: Att_DVCState)
    {
        dvc.latest_attestation_duty.isPresent()
        ==>
        ( forall att_duty | att_duty in dvc.all_rcvd_duties ::
            att_duty.slot <= dvc.latest_attestation_duty.safe_get().slot
        )
    }

    predicate inv_no_rcvd_att_duties_are_higher_than_latest_att_duty(dv: Att_DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            &&  var dvc := dv.honest_nodes_states[hn];
            &&  inv_no_rcvd_att_duties_are_higher_than_latest_att_duty_body(dvc)
    }

    
    predicate inv_data_of_all_created_attestations_is_a_set_of_decided_values(dv: Att_DVState)
    {
        forall a | a in dv.all_attestations_created ::
                && var consa := dv.consensus_on_attestation_data[a.data.slot];
                && consa.decided_value.isPresent() 
                && a.data == consa.decided_value.safe_get() 
    }

    // predicate inv_one_honest_dvc_is_required_to_pass_signer_threshold(
    //     dv: Att_DVState,
    //     signers: set<BLSPubkey>,
    //     att_shares: set<AttestationShare>,
    //     signing_root: Root
    // )
    // {
    //     (
    //         && signer_threshold(signers, att_shares, signing_root)
    //         && signers <= dv.all_nodes
    //     )
    //     ==>
    //     (
    //         exists h_node ::
    //             && h_node in signers
    //             && is_an_honest_node(dv, h_node)
    //     )
    // }

    predicate inv_all_created_attestations_are_valid(dv: Att_DVState)
    {
        forall a | a in dv.all_attestations_created ::
                is_valid_attestation(a, dv.dv_pubkey)
    }

    predicate inv_outputs_attestations_submited_are_valid(
        outputs: Outputs,
        dv_pubkey: BLSPubkey)
    {
        forall submitted_attestation | submitted_attestation in outputs.submitted_data ::
            is_valid_attestation(submitted_attestation, dv_pubkey)
    }

    // predicate pred_the_subset_relation_of_db_hist_on_slots_body(
    //             set_db:  set<set<SlashingDBAttestation>>,
    //             set_db':  set<set<SlashingDBAttestation>>
    // )
    // {
    //     forall db, db', sdba |
    //         && db in set_db
    //         && db' in set_db'
    //         ::
    //         (   sdba in db
    //             ==>
    //             sdba in db'
    //         )
    // }

    // predicate pred_the_subset_relation_of_db_hist_on_slots(
    //     db_hist_on_slot: map<AttestationData -> bool, set<set<SlashingDBAttestation>>>,
    //     db_hist_on_slot': map<AttestationData -> bool, set<set<SlashingDBAttestation>>>
    // )
    // {
    //     forall vp, vp' |
    //         && vp in db_hist_on_slot.Keys
    //         && vp' in db_hist_on_slot'.Keys 
    //         ::
    //         pred_the_subset_relation_of_db_hist_on_slots_body(
    //             db_hist_on_slot[vp],
    //             db_hist_on_slot'[vp']
    //         )
             
    // }

    predicate pred_is_the_owner_of_att_share(
        rs_pubkey: BLSPubkey,
        att_share: AttestationShare
    )
    {
        && var decided_attestation_data := att_share.data;
        && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
        && var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
        && verify_bls_signature(attestation_signing_root, att_share.signature, rs_pubkey)
    }

    predicate inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db_body(
        dvc: Att_DVCState, 
        att_share: AttestationShare
    )
    {
        && var att_data: AttestationData := att_share.data;
        && var slashing_db_attestation := construct_SlashingDBAttestation_from_att_data(att_data);
        && slashing_db_attestation in dvc.attestation_slashing_db  
        && var rs_pubkey: BLSPubkey := dvc.rs.pubkey;    
        && pred_is_the_owner_of_att_share(rs_pubkey, att_share)
    }   

    predicate inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db(
        outputs: Outputs,
        dvc: Att_DVCState)
    {
        forall att_share: AttestationShare | 
            att_share in getMessagesFromMessagesWithRecipient(outputs.att_shares_sent) 
            ::
            inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db_body(dvc, att_share)
    } 

    predicate inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body(
        dvc: Att_DVCState
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
            && pred_is_the_owner_of_att_share(rs_pubkey, att_share)
    }   

    predicate inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db(
        dv: Att_DVState)
    {
        forall hn: BLSPubkey | 
            is_an_honest_node(dv, hn)
            ::
            inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body(dv.honest_nodes_states[hn])
    } 

    predicate inv_sent_att_shares_have_corresponding_slashing_db_attestations_body(
        dvc: Att_DVCState,
        att_share: AttestationShare
    )
    {
        && var att_data := att_share.data;
        && var slashing_db_attestation := construct_SlashingDBAttestation_from_att_data(att_data);
        && slashing_db_attestation in dvc.attestation_slashing_db     
    }

    predicate inv_sent_att_shares_have_corresponding_slashing_db_attestations(
        dv: Att_DVState
    )
    {
        forall hn: BLSPubkey, att_share: AttestationShare | 
            && is_an_honest_node(dv, hn)
            && att_share in dv.att_network.allMessagesSent 
            && var dvc: Att_DVCState := dv.honest_nodes_states[hn];
            && var rs_pubkey: BLSPubkey := dvc.rs.pubkey;
            && pred_is_the_owner_of_att_share(rs_pubkey, att_share)
            ::
            && var dvc: Att_DVCState := dv.honest_nodes_states[hn];
            && inv_sent_att_shares_have_corresponding_slashing_db_attestations_body(dvc, att_share)            
    }

    predicate inv_an_attestation_is_created_based_on_shares_of_a_quorum_body_signers_helper(
        att_shares: set<AttestationShare>,
        dvc: Att_DVCState
    )
    {
        exists att_share: AttestationShare ::
            && att_share in att_shares
            && var rs_pubkey := dvc.rs.pubkey;
            && pred_is_the_owner_of_att_share(rs_pubkey, att_share)
    }

    predicate inv_an_attestation_is_created_based_on_shares_of_a_quorum_body_signers(
        dv: Att_DVState,
        att_shares: set<AttestationShare>,
        dvc_signer_pubkeys: set<BLSPubkey>
    )
    {
        forall key: BLSPubkey | key in dvc_signer_pubkeys ::
            key in dv.honest_nodes_states.Keys
            ==>
            inv_an_attestation_is_created_based_on_shares_of_a_quorum_body_signers_helper(
                    att_shares,
                    dv.honest_nodes_states[key]
                )        
    }

    predicate inv_an_attestation_is_created_based_on_shares_of_a_quorum_body_helper(
        dv: Att_DVState, 
        att: Attestation,
        att_shares: set<AttestationShare>, 
        signers: set<BLSPubkey>
    )
    {
        && att_shares <= dv.att_network.allMessagesSent
        && var constructed_sig := dv.construct_signed_attestation_signature(att_shares);
        && constructed_sig.isPresent()
        && constructed_sig.safe_get() == att.signature
        && all_att_shares_have_the_same_data(att_shares, att.data)
        && signers <= dv.all_nodes
        && inv_an_attestation_is_created_based_on_shares_of_a_quorum_body_signers(dv, att_shares, signers)
        && |signers| >= quorum(|dv.all_nodes|)
    }

    predicate inv_an_attestation_is_created_based_on_shares_of_a_quorum_body(
        dv: Att_DVState, 
        att: Attestation        
    )
    {
        exists att_shares, dvc_signer_pubkeys :: 
                && att_shares <= dv.att_network.allMessagesSent
                && var constructed_sig := dv.construct_signed_attestation_signature(att_shares);
                && constructed_sig.isPresent()
                && constructed_sig.safe_get() == att.signature
                && all_att_shares_have_the_same_data(att_shares, att.data)
                && dvc_signer_pubkeys <= dv.all_nodes
                && inv_an_attestation_is_created_based_on_shares_of_a_quorum_body_signers(dv, att_shares, dvc_signer_pubkeys)
                && |dvc_signer_pubkeys| >= quorum(|dv.all_nodes|)
    }

    predicate inv_an_attestation_is_created_based_on_shares_of_a_quorum(dv: Att_DVState)
    {
        forall att: Attestation | att in dv.all_attestations_created ::
                inv_an_attestation_is_created_based_on_shares_of_a_quorum_body(dv, att)
    }

    predicate inv_an_attestation_is_created_based_shares_from_a_quorum_of_rs_signers_body(
        att_shares: set<AttestationShare>,
        rs_signer_pubkey: BLSPubkey
    )
    {
        exists att_share: AttestationShare ::
            && att_share in att_shares
            && pred_is_the_owner_of_att_share(rs_signer_pubkey, att_share)
    }

    predicate inv_an_attestation_is_created_based_shares_from_a_quorum_of_rs_signers(
        att_shares: set<AttestationShare>,
        rs_signer_pubkeys: set<BLSPubkey>
    )
    {
        forall key: BLSPubkey | key in rs_signer_pubkeys ::
                inv_an_attestation_is_created_based_shares_from_a_quorum_of_rs_signers_body(
                    att_shares,
                    key
                )        
    }

    predicate inv_outputs_attestations_submited_are_created_based_on_shares_of_a_quorum_body(
        dvc: Att_DVCState, 
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
                && all_att_shares_have_the_same_data(att_shares, att.data)
                && inv_an_attestation_is_created_based_shares_from_a_quorum_of_rs_signers(att_shares, rs_signer_pubkeys)
                && |rs_signer_pubkeys| >= quorum(|dvc.peers|)
                && rs_signer_pubkeys <= dvc.peers
    }   

    predicate inv_outputs_attestations_submited_are_created_based_on_shares_of_a_quorum(
        outputs: Outputs,
        dvc: Att_DVCState)
    {
        forall submitted_attestation | submitted_attestation in outputs.submitted_data ::
            inv_outputs_attestations_submited_are_created_based_on_shares_of_a_quorum_body(dvc, submitted_attestation)
    } 

    predicate inv_db_of_vp_contains_all_data_of_sent_att_shares_with_lower_slots_body(
        dv: Att_DVState,
        hn: BLSPubkey,
        slot: Slot, 
        vp: AttestationData -> bool, 
        db: set<SlashingDBAttestation>
    )
    {
        forall att_share: AttestationShare | 
            && att_share in dv.att_network.allMessagesSent
            && is_an_honest_node(dv, hn)
            && var dvc := dv.honest_nodes_states[hn];
            && var rs_pubkey := dvc.rs.pubkey;
            && pred_is_the_owner_of_att_share(rs_pubkey, att_share)
            && att_share.data.slot < slot
            ::
            && var att_data := att_share.data;
            && var slashing_db_attestation := SlashingDBAttestation(
                                            source_epoch := att_data.source.epoch,
                                            target_epoch := att_data.target.epoch,
                                            signing_root := Some(hash_tree_root(att_data)));
            && slashing_db_attestation in db
    }

    predicate inv_db_of_vp_contains_all_data_of_sent_att_shares_with_lower_slots(dv: Att_DVState)
    {
        forall hn: BLSPubkey, slot: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation> | 
            && is_an_honest_node(dv, hn) 
            && var dvc := dv.honest_nodes_states[hn];
            && slot in dvc.attestation_consensus_engine_state.att_slashing_db_hist
            && vp in dvc.attestation_consensus_engine_state.att_slashing_db_hist[slot].Keys
            && db in dvc.attestation_consensus_engine_state.att_slashing_db_hist[slot][vp]
            :: 
            inv_db_of_vp_contains_all_data_of_sent_att_shares_with_lower_slots_body(
                dv,
                hn,
                slot,
                vp,
                db)
    }

    predicate inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_body(
        allMessagesSent: set<AttestationShare>,
        rs_pubkey: BLSPubkey,
        slot: Slot, 
        vp: AttestationData -> bool, 
        db: set<SlashingDBAttestation>
    )
    {
        forall att_share: AttestationShare | 
            && att_share in allMessagesSent
            && pred_is_the_owner_of_att_share(rs_pubkey, att_share)
            && att_share.data.slot < slot
            ::
            && var att_data := att_share.data;
            && var slashing_db_attestation := SlashingDBAttestation(
                                            source_epoch := att_data.source.epoch,
                                            target_epoch := att_data.target.epoch,
                                            signing_root := Some(hash_tree_root(att_data)));
            && slashing_db_attestation in db
    }

    predicate inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc(
        allMessagesSent: set<AttestationShare>,
        dvc: Att_DVCState        
    )
    {
        forall slot: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation> | 
            && slot in dvc.attestation_consensus_engine_state.att_slashing_db_hist
            && vp in dvc.attestation_consensus_engine_state.att_slashing_db_hist[slot].Keys
            && db in dvc.attestation_consensus_engine_state.att_slashing_db_hist[slot][vp]
            :: 
            inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_body(
                allMessagesSent,
                dvc.rs.pubkey,
                slot,
                vp,
                db
            )
    }

    predicate inv_unchanged_dvc_rs_pubkey(dv: Att_DVState)
    {
        forall hn: BLSPubkey | is_an_honest_node(dv, hn) ::
            && var dvc: Att_DVCState := dv.honest_nodes_states[hn];
            && dvc.rs.pubkey == hn
    }

    predicate inv_honest_nodes_are_not_owners_of_att_shares_from_adversary_body(
        dv: Att_DVState, 
        att_share: AttestationShare
    )
    {
        forall hn: BLSPubkey | is_an_honest_node(dv, hn) :: 
            !pred_is_the_owner_of_att_share(hn, att_share)
    }

    predicate inv_honest_nodes_are_not_owners_of_att_shares_from_adversary(dv: Att_DVState)
    {
        forall byz_node: BLSPubkey, att_share: AttestationShare | 
            && byz_node in dv.adversary.nodes 
            && att_share in dv.att_network.allMessagesSent
            && pred_is_the_owner_of_att_share(byz_node, att_share)
            ::
            inv_honest_nodes_are_not_owners_of_att_shares_from_adversary_body(dv, att_share)
    }
}