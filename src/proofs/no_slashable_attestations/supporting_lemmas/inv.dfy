include "../../../common/commons.dfy"
include "../common/dvc_attestation_creation_instrumented.dfy"
include "../../../specs/dvc/consensus_engine.dfy"
include "../../../specs/consensus/consensus.dfy"
include "../../../specs/network/network.dfy"
include "../../../specs/dv/dv_attestation_creation.dfy"
include "../../bn_axioms.dfy"
include "../../rs_axioms.dfy"


module Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
{
    import opened Types 
    import opened Common_Functions
    import opened Set_Seq_Helper
    import opened Signing_Methods
    import opened Consensus
    import opened Network_Spec
    import opened Att_DVC
    import opened Att_DV
    import opened Att_DV_Assumptions
    import opened BN_Axioms
    import opened RS_Axioms
    import opened Consensus_Engine

    predicate is_honest_node(s: AttDVState, n: BLSPubkey)
    {
        n in s.honest_nodes_states.Keys
    }

    predicate inv_rcvd_attestation_shares_are_sent_messages_body(
        dv: AttDVState,
        dvc: AttDVCState
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
        dv: AttDVState    
    )
    {
        forall n | n in dv.honest_nodes_states.Keys ::
            inv_rcvd_attestation_shares_are_sent_messages_body(dv, dv.honest_nodes_states[n])
    }  

    predicate inv_exists_honest_node_that_sent_att_share_for_every_submitted_att_body(
        dv: AttDVState,
        hn: BLSPubkey, 
        att_share: AttestationShare,
        a: Attestation
    )
    {
        && hn in dv.honest_nodes_states.Keys 
        && att_share in dv.att_network.allMessagesSent
        && att_share.data == a.data
        && var fork_version := af_bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));
        && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
        && verify_bls_signature(attestation_signing_root, att_share.signature, hn)
    }

    predicate inv_exists_honest_node_that_sent_att_share_for_every_submitted_att(dv: AttDVState)
    {
        forall a |
            && a in dv.all_attestations_created
            && att_signature_is_signed_with_pubkey(a, dv.dv_pubkey)
            ::
            exists hn, att_share: AttestationShare :: inv_exists_honest_node_that_sent_att_share_for_every_submitted_att_body(dv, hn, att_share, a)
    }

    predicate inv_data_of_att_shares_are_decided_values(dv: AttDVState)
    {
        forall hn, att_share |
                && hn in dv.honest_nodes_states.Keys 
                && att_share in dv.att_network.allMessagesSent
                && var fork_version := af_bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));                
                && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
                && verify_bls_signature(attestation_signing_root, att_share.signature, hn)
            ::
                inv_data_of_att_shares_are_decided_values_body(dv, att_share)
    }  

    predicate inv_data_of_att_shares_are_decided_values_body(dv: AttDVState, att_share: AttestationShare)
    {
        && dv.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent()
        && dv.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data
    }  

    predicate inv_decided_values_of_consensus_instances_are_decided_by_quorum(dv: AttDVState)
    {
        forall cid |
            && cid in dv.consensus_on_attestation_data.Keys
            && dv.consensus_on_attestation_data[cid].decided_value.isPresent()
            ::
            decided_value_is_valid(dv.consensus_on_attestation_data[cid])
    }  

    predicate inv_decided_value_of_consensus_instance_for_slot_k_is_for_slot_k(dv: AttDVState)
    {
        forall cid |
            && cid in dv.consensus_on_attestation_data.Keys
            && dv.consensus_on_attestation_data[cid].decided_value.isPresent()
            ::
            dv.consensus_on_attestation_data[cid].decided_value.safe_get().slot == cid
    }     

    predicate inv_every_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_body(
        s: Slot,
        attestation_duty: AttestationDuty,
        attestation_slashing_db: set<SlashingDBAttestation>,
        vp: AttestationData -> bool
    )
    {
        && attestation_duty.slot == s
        && (vp == (ad: AttestationData) => ci_decision_att_signature_is_signed_with_pubkey_data(attestation_slashing_db, ad, attestation_duty))
    }

    predicate inv_every_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(dv: AttDVState)
    {
        forall hn, s: Slot, vp |
            && hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
            && vp in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions[hn]
            ::
            exists attestation_duty, attestation_slashing_db ::
                inv_every_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_body(s, attestation_duty, attestation_slashing_db, vp)
    }    

    predicate inv_exists_slashing_db_for_given_att_duty_and_vp(
        cid: Slot,
        attestation_duty: AttestationDuty,
        vp: AttestationData -> bool
    )
    {
        exists attestation_slashing_db ::
            inv_every_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_body(cid, attestation_duty, attestation_slashing_db, vp)        
    }      
    
    predicate inv_every_active_consensus_instance_has_corresponding_att_duty_and_validity_predicate(
        dv: AttDVState,
        n: BLSPubkey,
        cid: Slot
    )
    requires n in dv.honest_nodes_states.Keys 
    requires cid in dv.honest_nodes_states[n].attestation_consensus_engine_state.active_consensus_instances.Keys
    {
        &&  var dvc := dv.honest_nodes_states[n];
        &&  var acvc := dvc.attestation_consensus_engine_state.active_consensus_instances[cid];
        &&  inv_exists_slashing_db_for_given_att_duty_and_vp(
                cid, 
                acvc.attestation_duty, 
                acvc.validityPredicate
            ) 
    }

    predicate inv_exist_att_duty_and_validity_predicate_for_active_consensus_instance_at_slot_cid(
        dvc: AttDVCState,
        cid: Slot
    )
    requires cid in dvc.attestation_consensus_engine_state.active_consensus_instances.Keys
    {
        &&  var acvc := dvc.attestation_consensus_engine_state.active_consensus_instances[cid];
        &&  inv_exists_slashing_db_for_given_att_duty_and_vp(
                cid, 
                acvc.attestation_duty, 
                acvc.validityPredicate
            ) 
    }     

    predicate inv_every_active_consensus_instance_of_dvc_has_corresponding_att_duty_and_validity_predicate(dvc: AttDVCState)
    {
        forall cid | 
            && cid in dvc.attestation_consensus_engine_state.active_consensus_instances.Keys
            ::
            inv_exist_att_duty_and_validity_predicate_for_active_consensus_instance_at_slot_cid(dvc, cid)        
    }    

    predicate inv_every_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(dv: AttDVState)
    {
        forall n, cid | 
            && n in dv.honest_nodes_states.Keys
            && cid in dv.honest_nodes_states[n].attestation_consensus_engine_state.active_consensus_instances.Keys
            ::
            inv_every_active_consensus_instance_has_corresponding_att_duty_and_validity_predicate(dv, n, cid)
    }  

    predicate inv_exists_att_duty_in_dv_seq_of_att_duties_for_every_slot_in_slashing_db_hist(dv: AttDVState)    
    {
        forall hn | hn in dv.honest_nodes_states.Keys          
            ::
            inv_exists_att_duty_in_dv_seq_of_att_duties_for_every_slot_in_slashing_db_hist_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn],
                dv.index_next_attestation_duty_to_be_served
            )                    
    }       

    predicate inv_exists_att_duty_in_dv_seq_of_att_duties_for_every_slot_in_slashing_db_hist_body(
        dv: AttDVState, 
        n: BLSPubkey,
        n_state: AttDVCState,
        index_next_attestation_duty_to_be_served: nat
    )
    {
        forall slot  |
            && slot in n_state.attestation_consensus_engine_state.slashing_db_hist.Keys
            ::
            exists i: Slot :: 
                && i < index_next_attestation_duty_to_be_served
                && var an := dv.sequence_of_attestation_duties_to_be_served[i];
                && an.attestation_duty.slot == slot 
                && an.node == n
    }   

    function f_get_upperlimit_active_instances(
        n_state: AttDVCState
    ): nat 
    {
        if n_state.latest_attestation_duty.isPresent() then
            n_state.latest_attestation_duty.safe_get().slot + 1
        else
            0
    }                

    predicate inv_slots_of_consensus_instances_are_up_to_slot_of_latest_att_duty_body(dvc: AttDVCState)
    {
        forall slot: Slot |
            && slot in dvc.attestation_consensus_engine_state.slashing_db_hist.Keys
            ::
            slot < f_get_upperlimit_active_instances(dvc)
    }     

    predicate inv_slots_of_consensus_instances_are_up_to_slot_of_latest_att_duty(dv: AttDVState)
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
                inv_slots_of_consensus_instances_are_up_to_slot_of_latest_att_duty_body(dv.honest_nodes_states[hn])        
    }     
    
    predicate inv_latest_att_duty_is_from_dv_seq_of_att_duties(dv: AttDVState)    
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
        dv: AttDVState, 
        n: BLSPubkey,
        n_state: AttDVCState,
        index_next_attestation_duty_to_be_served: nat
    )
    {
        n_state.latest_attestation_duty.isPresent() 
        ==>
        exists i: Slot :: 
            && i < index_next_attestation_duty_to_be_served
            && var an := dv.sequence_of_attestation_duties_to_be_served[i];
            && an.attestation_duty == n_state.latest_attestation_duty.safe_get()
            && an.node == n
    }     

    predicate pred_exists_att_duty_from_dv_seq_of_att_duties_for_given_att_duty(  
        attestation_duty: AttestationDuty,
        hn: BLSPubkey,
        sequence_of_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    {
        exists i: Slot :: 
            && i < index_next_attestation_duty_to_be_served
            && var an := sequence_of_attestation_duties_to_be_served[i];
            && an.attestation_duty == attestation_duty
            && an.node == hn
    } 

    predicate inv_available_latest_att_duty_is_from_dv_seq_of_att_duties(  
        n: BLSPubkey,
        n_state: AttDVCState,
        sequence_of_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    {
        n_state.latest_attestation_duty.isPresent()
        ==>
        exists i: Slot :: 
            && i < index_next_attestation_duty_to_be_served
            && var an := sequence_of_attestation_duties_to_be_served[i];
            && an.attestation_duty == n_state.latest_attestation_duty.safe_get()
            && an.node == n
    }  

    predicate inv_future_decisions_known_by_dvc_are_decisions_of_quorums(dv: AttDVState)    
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
        dv: AttDVState, 
        n: BLSPubkey,
        n_state: AttDVCState
    )
    {
        forall slot |
            && slot in n_state.future_att_consensus_instances_already_decided.Keys
            ::
            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
            && n_state.future_att_consensus_instances_already_decided[slot] == dv.consensus_on_attestation_data[slot].decided_value.safe_get()
    }  

    predicate inv_slots_in_future_decided_data_are_correct(dv: AttDVState)    
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
        dv: AttDVState, 
        n: BLSPubkey,
        n_state: AttDVCState
    )
    {
        forall slot | slot in n_state.future_att_consensus_instances_already_decided.Keys
            ::
            n_state.future_att_consensus_instances_already_decided[slot].slot == slot
    }       

    predicate inv_domain_of_active_consensus_instances_is_subset_of_slashing_db_hist(dv: AttDVState)    
    {
        forall hn |hn in dv.honest_nodes_states.Keys  ::
            inv_domain_of_active_consensus_instances_is_subset_of_slashing_db_hist_body(
                dv.honest_nodes_states[hn]
            )                    
    }       

    predicate inv_domain_of_active_consensus_instances_is_subset_of_slashing_db_hist_body(n_state: AttDVCState)
    {
        n_state.attestation_consensus_engine_state.active_consensus_instances.Keys <= n_state.attestation_consensus_engine_state.slashing_db_hist.Keys
    }

    predicate inv_active_consensus_instances_predicate_is_in_slashing_db_hist(dv: AttDVState)    
    {
        forall hn, cid | hn in dv.honest_nodes_states.Keys ::
            inv_validitty_predicates_of_active_consensus_instances_are_tracked_in_slashing_db_hist_body(dv.honest_nodes_states[hn], cid)
             
    }       

    predicate inv_validitty_predicates_of_active_consensus_instances_are_tracked_in_slashing_db_hist_body(
        n_state: AttDVCState,
        cid: Slot
    )
    {
        cid in n_state.attestation_consensus_engine_state.active_consensus_instances.Keys
        ==>
        (
            && cid in n_state.attestation_consensus_engine_state.slashing_db_hist
            && n_state.attestation_consensus_engine_state.active_consensus_instances[cid].validityPredicate in n_state.attestation_consensus_engine_state.slashing_db_hist[cid] 
        )
    }    

    predicate inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(
        dvc: AttDVCState,
        hn: BLSPubkey,
        sequence_of_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    {
       forall att_duty |
            att_duty in dvc.all_rcvd_duties
            ::
            inv_exists_att_duty_in_dv_seq_of_att_duties_for_given_att_duty(                
                att_duty, 
                hn, 
                sequence_of_attestation_duties_to_be_served,
                index_next_attestation_duty_to_be_served)
    }

    predicate inv_rcvd_att_duties_are_from_dv_seq_of_att_duties(dv: AttDVState)
    {
        forall hn: BLSPubkey | 
            is_honest_node(dv, hn) 
            ::
            && var hn_state := dv.honest_nodes_states[hn];
            && inv_rcvd_att_duties_are_from_dv_seq_of_att_duties_body(                    
                    hn_state, 
                    hn, 
                    dv.sequence_of_attestation_duties_to_be_served,
                    dv.index_next_attestation_duty_to_be_served)
    }

    predicate inv_exists_att_duty_in_dv_seq_of_att_duties_for_given_att_duty(        
        att_duty: AttestationDuty,
        hn: BLSPubkey, 
        sequence_of_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    {
        exists i ::
            && 0 <= i
            && i < index_next_attestation_duty_to_be_served 
            && var duty_and_node := sequence_of_attestation_duties_to_be_served[i];
            && duty_and_node.node == hn
            && duty_and_node.attestation_duty == att_duty
    }  

    predicate inv_sent_validity_predicates_are_only_for_slots_stored_in_slashing_db_hist(dv: AttDVState)
    {
        forall hn: BLSPubkey, s: Slot | is_honest_node(dv, hn) ::
            && var hn_state := dv.honest_nodes_states[hn];
            && ( hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
                 ==> 
                 s in hn_state.attestation_consensus_engine_state.slashing_db_hist.Keys)
    }

    predicate inv_all_validity_predicates_are_stored_in_slashing_db_hist_body(
        dv: AttDVState, 
        hn: BLSPubkey,
        hn_state: AttDVCState,
        s: Slot,
        vp: AttestationData -> bool
    )
    requires hn in dv.honest_nodes_states.Keys
    {
        (
            && var hn_state := dv.honest_nodes_states[hn];
            && hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
            && s in hn_state.attestation_consensus_engine_state.slashing_db_hist.Keys
            && vp in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions[hn]
        )
            ==>
        (
            && var hn_state := dv.honest_nodes_states[hn];
            && vp in hn_state.attestation_consensus_engine_state.slashing_db_hist[s]   
        )             
    }       
    
    predicate inv_all_validity_predicates_are_stored_in_slashing_db_hist(dv: AttDVState)
    {
        forall hn: BLSPubkey, s: Slot, vp : AttestationData -> bool |
            hn in dv.honest_nodes_states.Keys
            ::
            inv_all_validity_predicates_are_stored_in_slashing_db_hist_body(
                dv,
                hn,
                dv.honest_nodes_states[hn],
                s,
                vp
            )
    }              

    predicate inv_unique_rcvd_att_duty_per_slot(dv: AttDVState)
    {
        forall hn: BLSPubkey | 
            is_honest_node(dv, hn) 
            ::
            inv_unique_rcvd_att_duty_per_slot_body(dv.honest_nodes_states[hn])
    }

    predicate inv_unique_rcvd_att_duty_per_slot_body(dvc: AttDVCState)
    {
        forall d1: AttestationDuty, d2: AttestationDuty | 
            && d1 in dvc.all_rcvd_duties
            && d2 in dvc.all_rcvd_duties
            && d1.slot == d2.slot
            ::
            d1 == d2
    }

    predicate inv_every_sent_validity_predicate_is_based_on_existing_slashing_db_and_rcvd_att_duty_body(
        dv: AttDVState, 
        hn: BLSPubkey, 
        s: Slot, 
        db: set<SlashingDBAttestation>, 
        duty: AttestationDuty, 
        vp: AttestationData -> bool)
    requires && is_honest_node(dv, hn)
             && var hn_state := dv.honest_nodes_states[hn];
             && s in hn_state.attestation_consensus_engine_state.slashing_db_hist.Keys
             && vp in hn_state.attestation_consensus_engine_state.slashing_db_hist[s].Keys
    {
        && var hn_state := dv.honest_nodes_states[hn];
        && duty.slot == s
        && db in hn_state.attestation_consensus_engine_state.slashing_db_hist[s][vp]
        && vp == (ad: AttestationData) => ci_decision_att_signature_is_signed_with_pubkey_data(db, ad, duty)
    }

    predicate inv_every_sent_validity_predicate_is_based_on_existing_slashing_db_and_rcvd_att_duty(dv: AttDVState)
    {
        forall hn: BLSPubkey, s: Slot, vp: AttestationData -> bool | 
            && is_honest_node(dv, hn)
            && var hn_state := dv.honest_nodes_states[hn];
            && s in hn_state.attestation_consensus_engine_state.slashing_db_hist.Keys
            && vp in hn_state.attestation_consensus_engine_state.slashing_db_hist[s].Keys
            ::
            exists duty, db ::
                && var hn_state := dv.honest_nodes_states[hn];
                && inv_every_sent_validity_predicate_is_based_on_existing_slashing_db_and_rcvd_att_duty_body(dv, hn, s, db, duty, vp)
    }

    predicate inv_every_decided_data_has_honest_witness_body<D(!new, 0)>(ci: ConsensusInstance) 
    {
        ci.decided_value.isPresent()
        ==> 
        decided_value_is_valid(ci)
    }
    
    predicate inv_every_decided_data_has_honest_witness(dv: AttDVState)
    {
        forall s: Slot ::
            && var ci := dv.consensus_on_attestation_data[s];
            && inv_every_decided_data_has_honest_witness_body(ci)            
    }

    predicate same_honest_nodes_in_dv_and_ci(dv: AttDVState)
    {
        forall s: Slot ::
            && var ci := dv.consensus_on_attestation_data[s];            
            && dv.all_nodes == ci.all_nodes
            && dv.honest_nodes_states.Keys == ci.honest_nodes_status.Keys
    }

    predicate inv_all_honest_nodes_is_quorum(dv: AttDVState)
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

    predicate inv_unchanged_paras_of_consensus_instances(dv: AttDVState)
    {
        forall ci | ci in dv.consensus_on_attestation_data.Values
            :: && ci.all_nodes == dv.all_nodes
               && ci.honest_nodes_status.Keys == dv.honest_nodes_states.Keys  
               && ci.honest_nodes_status.Keys <= ci.all_nodes
               && ci.honest_nodes_validity_functions.Keys <= ci.honest_nodes_status.Keys
               && |ci.all_nodes - ci.honest_nodes_status.Keys| <= f(|ci.all_nodes|)
    }

    predicate inv_only_dv_construct_signed_attestation_signature(dv: AttDVState)
    {
        && assump_construction_of_signed_attestation_signatures(
                dv.construct_signed_attestation_signature,
                dv.dv_pubkey,
                dv.all_nodes
            )                
        && forall n | n in dv.honest_nodes_states.Keys :: 
                && var nodes := dv.honest_nodes_states[n];
                && nodes.construct_signed_attestation_signature == dv.construct_signed_attestation_signature
                && nodes.dv_pubkey == dv.dv_pubkey       
                && nodes.peers == dv.all_nodes
    }

    predicate inv_current_att_duty_is_rcvd_duty_body(dvc: AttDVCState)
    {
        dvc.current_attestation_duty.isPresent()
        ==> 
        dvc.current_attestation_duty.safe_get() in dvc.all_rcvd_duties
    }

    predicate inv_current_att_duty_is_rcvd_duty(dv: AttDVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_current_att_duty_is_rcvd_duty_body(dvc)
    }

    predicate inv_latest_att_duty_is_rcvd_duty_body(dvc: AttDVCState)
    {
        dvc.latest_attestation_duty.isPresent()
        ==> 
        dvc.latest_attestation_duty.safe_get() in dvc.all_rcvd_duties
    }

    predicate inv_latest_att_duty_is_rcvd_duty(dv: AttDVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_latest_att_duty_is_rcvd_duty_body(dvc)
    }

    predicate inv_none_latest_att_duty_implies_none_current_att_duty_body(dvc: AttDVCState)
    {
        !dvc.latest_attestation_duty.isPresent()
        ==> 
        !dvc.current_attestation_duty.isPresent()
    }

    predicate inv_none_latest_att_duty_implies_none_current_att_duty(dv: AttDVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_none_latest_att_duty_implies_none_current_att_duty_body(dvc)
    }
  
    predicate inv_current_att_duty_is_either_none_or_latest_att_duty_body(dvc: AttDVCState)
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

    predicate inv_current_att_duty_is_either_none_or_latest_att_duty(dv: AttDVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_current_att_duty_is_either_none_or_latest_att_duty_body(dvc)
    }

    predicate inv_available_current_att_duty_is_latest_att_duty_body(dvc: AttDVCState)
    {
        dvc.current_attestation_duty.isPresent()
        ==> 
        ( && dvc.latest_attestation_duty.isPresent()
          && dvc.current_attestation_duty.safe_get()
                                == dvc.latest_attestation_duty.safe_get()                   
        )
    }

    predicate inv_available_current_att_duty_is_latest_att_duty(dv: AttDVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_available_current_att_duty_is_latest_att_duty_body(dvc)
    }

    predicate inv_att_duty_in_next_delivery_is_not_lower_than_current_att_duty_body(dvc: AttDVCState, next_duty: AttestationDuty)
    {
        dvc.current_attestation_duty.isPresent()
        ==> 
        dvc.current_attestation_duty.safe_get().slot <= next_duty.slot        
    }

    predicate inv_att_duty_in_next_delivery_is_not_lower_than_current_att_duty(dv: AttDVState)
    {
        && var dv_duty_queue := dv.sequence_of_attestation_duties_to_be_served;
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

    predicate inv_att_duty_in_next_delivery_is_not_lower_than_latest_att_duty_body(dvc: AttDVCState, next_duty: AttestationDuty)
    {
        dvc.latest_attestation_duty.isPresent()
        ==> 
        dvc.latest_attestation_duty.safe_get().slot <= next_duty.slot        
    }

    predicate inv_att_duty_in_next_delivery_is_not_lower_than_latest_att_duty(dv: AttDVState)
    {
        && var dv_duty_queue := dv.sequence_of_attestation_duties_to_be_served;
        && var dv_index := dv.index_next_attestation_duty_to_be_served;
        && var next_duty_and_node := dv_duty_queue[dv_index];
        && forall hn: BLSPubkey | 
            && hn in dv.honest_nodes_states.Keys
            && hn == next_duty_and_node.node 
            ::            
            && var dvc := dv.honest_nodes_states[hn];
            && var next_duty := next_duty_and_node.attestation_duty;
            && inv_att_duty_in_next_delivery_is_not_lower_than_latest_att_duty_body(dvc, next_duty)
    }

    predicate inv_att_duty_in_next_delivery_is_not_lower_than_rcvd_att_duties_body(dvc: AttDVCState, next_duty: AttestationDuty)
    {
       forall rcvd_duty: AttestationDuty | rcvd_duty in dvc.all_rcvd_duties ::
            rcvd_duty.slot <= next_duty.slot        
    }

    predicate inv_att_duty_in_next_delivery_is_not_lower_than_rcvd_att_duties(dv: AttDVState)
    {
        && var dv_duty_queue := dv.sequence_of_attestation_duties_to_be_served;
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

    predicate inv_in_transit_messages_are_in_allMessagesSent(
        dv: AttDVState
    )
    {
         forall m | m in dv.att_network.messagesInTransit ::
                m.message in dv.att_network.allMessagesSent       
    }

    predicate inv_attestation_shares_to_broadcast_is_subset_of_all_messages_sent_single_node(
        dv: AttDVState,
        n: BLSPubkey
    )
    requires n in dv.honest_nodes_states.Keys 
    {
        dv.honest_nodes_states[n].attestation_shares_to_broadcast.Values <= dv.att_network.allMessagesSent
    }

    predicate inv_attestation_shares_to_broadcast_is_subset_of_all_messages_sent(
        dv: AttDVState
    )
    {
        forall n | n in dv.honest_nodes_states.Keys ::
            inv_attestation_shares_to_broadcast_is_subset_of_all_messages_sent_single_node(dv, n)
    }    

    predicate inv_no_duplicated_att_duties(dv: AttDVState)
    {        
        && ( forall k1: Slot, k2: Slot ::
                && 0 <= k1
                && k1 < k2
                && dv.sequence_of_attestation_duties_to_be_served[k1].node 
                        in dv.honest_nodes_states.Keys
                && dv.sequence_of_attestation_duties_to_be_served[k1].node 
                        == dv.sequence_of_attestation_duties_to_be_served[k2].node 
                ==> 
                && var duty1 := dv.sequence_of_attestation_duties_to_be_served[k1].attestation_duty;
                && var duty2 := dv.sequence_of_attestation_duties_to_be_served[k2].attestation_duty;
                && duty1.slot < duty2.slot
           )
    }

    predicate pred_unchanged_dvn_seq_of_att_duties(dv: AttDVState, dv': AttDVState)
    {
        dv.sequence_of_attestation_duties_to_be_served
                == dv'.sequence_of_attestation_duties_to_be_served
    }

    predicate inv_every_att_duty_before_dv_att_index_was_delivered_body(dvc: AttDVCState, duty: AttestationDuty)
    {
        duty in dvc.all_rcvd_duties
    }

    predicate inv_every_att_duty_before_dv_att_index_was_delivered(dv: AttDVState)
    {
        forall k: nat ::
            && 0 <= k < dv.index_next_attestation_duty_to_be_served
            && dv.sequence_of_attestation_duties_to_be_served[k].node in dv.honest_nodes_states.Keys
            ==> 
            && var duty_and_node: AttestationDutyAndNode := dv.sequence_of_attestation_duties_to_be_served[k];
            && var duty := duty_and_node.attestation_duty;
            && var hn := duty_and_node.node;
            && var dvc := dv.honest_nodes_states[hn];
            && inv_every_att_duty_before_dv_att_index_was_delivered_body(dvc, duty)
    }    

    predicate inv_no_active_consensus_instances_before_first_att_duty_was_received_body(dvc: AttDVCState)
    {
        !dvc.latest_attestation_duty.isPresent()
        ==> 
        dvc.attestation_consensus_engine_state.active_consensus_instances.Keys == {}
    }

    predicate inv_no_active_consensus_instances_before_first_att_duty_was_received(dv: AttDVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_no_active_consensus_instances_before_first_att_duty_was_received_body(dvc)
    }
    
    predicate inv_slots_of_active_consensus_instances_are_not_higher_than_slot_of_latest_att_duty_body(dvc: AttDVCState)
    {
        dvc.latest_attestation_duty.isPresent()
        ==> ( forall k: Slot | k in dvc.attestation_consensus_engine_state.active_consensus_instances.Keys 
                ::
                k <= dvc.latest_attestation_duty.safe_get().slot
            )
    }

    predicate inv_slots_of_active_consensus_instances_are_not_higher_than_slot_of_latest_att_duty(dv: AttDVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_slots_of_active_consensus_instances_are_not_higher_than_slot_of_latest_att_duty_body(dvc)
    }

    predicate inv_dvc_has_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(dvc: AttDVCState)
    {
        forall k: Slot | k in dvc.attestation_consensus_engine_state.active_consensus_instances.Keys ::
            exists rcvd_duty: AttestationDuty :: 
                && rcvd_duty in dvc.all_rcvd_duties
                && rcvd_duty.slot == k
    }

    predicate inv_dvc_has_corresponding_att_duty_for_every_active_attestation_consensus_instance(dv: AttDVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_dvc_has_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(dvc)
    }

    predicate inv_consensus_instance_indexed_k_is_for_rcvd_duty_at_slot_k_body(dvc: AttDVCState)
    {
        forall k: Slot | k in dvc.attestation_consensus_engine_state.active_consensus_instances.Keys 
            ::
            && dvc.attestation_consensus_engine_state.active_consensus_instances[k].attestation_duty in dvc.all_rcvd_duties                
            && dvc.attestation_consensus_engine_state.active_consensus_instances[k].attestation_duty.slot == k
    }

    predicate inv_consensus_instance_indexed_k_is_for_rcvd_duty_at_slot_k(dv: AttDVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_consensus_instance_indexed_k_is_for_rcvd_duty_at_slot_k_body(dvc)
    }

    predicate inv_active_consensus_instances_imply_delivery_of_att_duties_body(hn_state: AttDVCState, s: Slot)
    requires s in hn_state.attestation_consensus_engine_state.slashing_db_hist.Keys
    {
        exists duty: AttestationDuty :: 
                    && duty in hn_state.all_rcvd_duties
                    && duty.slot == s
    }


    predicate inv_active_consensus_instances_imply_delivery_of_att_duties(dv: AttDVState)
    {
        forall hn: BLSPubkey, s: Slot ::
            ( && is_honest_node(dv, hn) 
              && var hn_state := dv.honest_nodes_states[hn];
              && s in hn_state.attestation_consensus_engine_state.slashing_db_hist.Keys
            )
            ==>
            inv_active_consensus_instances_imply_delivery_of_att_duties_body(dv.honest_nodes_states[hn], s)                
    }

    predicate inv_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(hn_state: AttDVCState)    
    {
        forall k: Slot | k in hn_state.attestation_consensus_engine_state.slashing_db_hist.Keys ::
            exists duty: AttestationDuty :: 
                    && duty in hn_state.all_rcvd_duties
                    && duty.slot == k
    }

    predicate inv_slashing_db_hist_keeps_track_only_of_rcvd_att_duties(dv: AttDVState)
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            && var hn_state := dv.honest_nodes_states[hn];            
            && inv_slashing_db_hist_keeps_track_only_of_rcvd_att_duties_body(hn_state)       
    }

    predicate inv_exist_db_in_slashing_db_hist_and_att_duty_for_every_validity_predicate_body_ces(ces: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>)
    {
        forall s: Slot, vp: AttestationData -> bool |
                ( && s in ces.slashing_db_hist.Keys
                  && vp in ces.slashing_db_hist[s].Keys
                )
                :: 
                ( exists db: set<SlashingDBAttestation>, duty: AttestationDuty ::
                        && duty.slot == s
                        && db in ces.slashing_db_hist[s][vp]
                        && vp == (ad: AttestationData) => ci_decision_att_signature_is_signed_with_pubkey_data(db, ad, duty)
                )
    }

    predicate inv_exist_db_in_slashing_db_hist_and_att_duty_for_every_validity_predicate_body(hn_state: AttDVCState)
    {
        forall s: Slot, vp: AttestationData -> bool |
                ( && s in hn_state.attestation_consensus_engine_state.slashing_db_hist.Keys
                  && vp in hn_state.attestation_consensus_engine_state.slashing_db_hist[s].Keys
                )
                :: 
                ( exists db: set<SlashingDBAttestation>, duty: AttestationDuty ::
                        && duty.slot == s
                        && db in hn_state.attestation_consensus_engine_state.slashing_db_hist[s][vp]
                        && vp == (ad: AttestationData) => ci_decision_att_signature_is_signed_with_pubkey_data(db, ad, duty)
                )
    }

    predicate inv_exist_db_in_slashing_db_hist_and_att_duty_for_every_validity_predicate(dv: AttDVState)
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_exist_db_in_slashing_db_hist_and_att_duty_for_every_validity_predicate_body(dvc)
    }

    predicate inv_current_validity_predicate_for_slot_k_is_stored_in_slashing_db_hist_k_body(hn_state: AttDVCState)
    {
        forall k: Slot |
            k in hn_state.attestation_consensus_engine_state.active_consensus_instances.Keys ::
                && var ci := hn_state.attestation_consensus_engine_state.active_consensus_instances[k];
                && var vp: AttestationData -> bool := ci.validityPredicate;
                && k in hn_state.attestation_consensus_engine_state.slashing_db_hist.Keys 
                && vp in hn_state.attestation_consensus_engine_state.slashing_db_hist[k].Keys             
    }

    predicate inv_current_validity_predicate_for_slot_k_is_stored_in_slashing_db_hist_k(dv: AttDVState)
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_current_validity_predicate_for_slot_k_is_stored_in_slashing_db_hist_k_body(dvc)
    }

    predicate inv_att_slashing_db_is_monotonic_body(dvc: AttDVCState, dvc': AttDVCState)
    {
        dvc.attestation_slashing_db <= dvc'.attestation_slashing_db
    }

    predicate inv_att_slashing_db_is_monotonic(dv: AttDVState, event: DVAttestationEvent, dv': AttDVState)    
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            && hn in dv'.honest_nodes_states.Keys
            && var dvc := dv.honest_nodes_states[hn];
            && var dvc' := dv'.honest_nodes_states[hn];
            && inv_att_slashing_db_is_monotonic_body(dvc, dvc')
    }

    predicate inv_every_db_in_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(ces: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>, attestation_slashing_db: set<SlashingDBAttestation>)
    {
        forall s: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation> |
                ( && s in ces.slashing_db_hist.Keys
                  && vp in ces.slashing_db_hist[s].Keys
                  && db in ces.slashing_db_hist[s][vp]
                )
                :: 
                db <= attestation_slashing_db
    }

    predicate inv_every_db_in_slashing_db_hist_is_subset_of_att_slashing_db_body(hn_state: AttDVCState)
    {
        forall s: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation> |
                ( && s in hn_state.attestation_consensus_engine_state.slashing_db_hist.Keys
                  && vp in hn_state.attestation_consensus_engine_state.slashing_db_hist[s].Keys
                  && db in hn_state.attestation_consensus_engine_state.slashing_db_hist[s][vp]
                )
                :: 
                db <= hn_state.attestation_slashing_db
    }

    predicate inv_every_db_in_slashing_db_hist_is_subset_of_att_slashing_db(dv: AttDVState)
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_every_db_in_slashing_db_hist_is_subset_of_att_slashing_db_body(dvc)
    }

    predicate inv_slashing_db_hist_is_monotonic_body(dvc: AttDVCState, dvc': AttDVCState)
    {        
        dvc.attestation_consensus_engine_state.slashing_db_hist.Keys
        <= 
        dvc'.attestation_consensus_engine_state.slashing_db_hist.Keys
    }

    predicate inv_slashing_db_hist_is_monotonic(dv: AttDVState, event: DVAttestationEvent, dv': AttDVState)    
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            && hn in dv'.honest_nodes_states.Keys
            && var dvc := dv.honest_nodes_states[hn];
            && var dvc' := dv'.honest_nodes_states[hn];
            && inv_slashing_db_hist_is_monotonic_body(dvc, dvc')
    }

    predicate inv_active_att_consensus_instances_are_tracked_in_slashing_db_hist_body(dvc: AttDVCState)
    {
        dvc.attestation_consensus_engine_state.active_consensus_instances.Keys 
        <= 
        dvc.attestation_consensus_engine_state.slashing_db_hist.Keys
    } 

    predicate inv_active_att_consensus_instances_are_tracked_in_slashing_db_hist(dv: AttDVState)
    {
        forall hn | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_active_att_consensus_instances_are_tracked_in_slashing_db_hist_body(dvc)
    } 

    predicate inv_only_dv_construct_signed_attestation_signatures(dv: AttDVState)
    {
        assump_construction_of_signed_attestation_signatures(
            dv.construct_signed_attestation_signature,
            dv.dv_pubkey,
            dv.all_nodes)
    }

    predicate inv_all_in_transit_messages_were_sent_body<M>(e: Network<M>)
    {
         forall m | m in e.messagesInTransit ::
                m.message in e.allMessagesSent       
    } 
     
    predicate inv_all_in_transit_messages_were_sent(dv: AttDVState)
    {
         forall m | m in dv.att_network.messagesInTransit ::
                m.message in dv.att_network.allMessagesSent       
    } 

    predicate inv_rcvd_att_shares_are_from_sent_messages_body(
        dv: AttDVState,
        dvc: AttDVCState
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
        dv: AttDVState    
    )
    {
        forall n | n in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[n];
            && inv_rcvd_att_shares_are_from_sent_messages_body(dv, dvc)
    } 

    predicate inv_attestation_shares_to_broadcast_are_sent_messages_body(
        dv: AttDVState,
        dvc: AttDVCState
    )    
    {
        dvc.attestation_shares_to_broadcast.Values <= dv.att_network.allMessagesSent
    }

    predicate inv_attestation_shares_to_broadcast_are_sent_messages(
        dv: AttDVState
    )
    {
        forall n | n in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[n];
            && inv_attestation_shares_to_broadcast_are_sent_messages_body(dv, dvc)
    }
  
    predicate inv_slots_for_sent_validity_predicates_are_stored_in_slashing_db_hist_body(
        dv: AttDVState, 
        hn: BLSPubkey,
        hn_state: AttDVCState,
        s: Slot
    )
    {
        hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
        ==> s in hn_state.attestation_consensus_engine_state.slashing_db_hist.Keys
    }

    predicate inv_slots_for_sent_validity_predicates_are_stored_in_slashing_db_hist(dv: AttDVState)
    {
        forall hn: BLSPubkey, s: Slot | hn in dv.honest_nodes_states.Keys :: 
            inv_slots_for_sent_validity_predicates_are_stored_in_slashing_db_hist_body(dv, hn, dv.honest_nodes_states[hn], s)        
    } 

    predicate inv_every_consensus_instance_condition_for_safety_is_true(dv: AttDVState)
    {
        forall slot: Slot | slot in dv.consensus_on_attestation_data.Keys  ::
                    condition_for_safety_is_true(dv.consensus_on_attestation_data[slot])                    
    }

    predicate pred_next_att_duty_is_delivering_to_given_honest_node(
        attestation_duty: AttestationDuty,
        dv: AttDVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    {
        && 0 < index_next_attestation_duty_to_be_served 
        && var i := index_next_attestation_duty_to_be_served - 1;
        && var an := dv.sequence_of_attestation_duties_to_be_served[i];
        && an.attestation_duty == attestation_duty
        && an.node == n
    }

    predicate inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_body(dvc: AttDVCState)
    {
        !dvc.latest_attestation_duty.isPresent()
        <==> 
        dvc.all_rcvd_duties == {}
    }

    predicate inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties(dv: AttDVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_body(dv.honest_nodes_states[hn])
    }

    predicate inv_no_rcvd_att_duties_are_higher_than_latest_att_duty_body(dvc: AttDVCState)
    {
        dvc.latest_attestation_duty.isPresent()
        ==>
        ( forall att_duty | att_duty in dvc.all_rcvd_duties ::
            att_duty.slot <= dvc.latest_attestation_duty.safe_get().slot
        )
    }

    predicate inv_no_rcvd_att_duties_are_higher_than_latest_att_duty(dv: AttDVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            &&  var dvc := dv.honest_nodes_states[hn];
            &&  inv_no_rcvd_att_duties_are_higher_than_latest_att_duty_body(dvc)
    }

    predicate inv_data_of_all_created_attestations_is_set_of_decided_values(dv: AttDVState)
    {
        forall a | a in dv.all_attestations_created ::
                && var consa := dv.consensus_on_attestation_data[a.data.slot];
                && consa.decided_value.isPresent() 
                && a.data == consa.decided_value.safe_get() 
    }

    predicate inv_all_created_attestations_are_valid(dv: AttDVState)
    {
        forall a | a in dv.all_attestations_created ::
                att_signature_is_signed_with_pubkey(a, dv.dv_pubkey)
    }

    predicate inv_outputs_attestations_submited_are_valid(
        outputs: AttestationOutputs,
        dv_pubkey: BLSPubkey)
    {
        forall submitted_attestation | submitted_attestation in outputs.submitted_data ::
            att_signature_is_signed_with_pubkey(submitted_attestation, dv_pubkey)
    }

    predicate pred_is_owner_of_att_share(
        rs_pubkey: BLSPubkey,
        att_share: AttestationShare
    )
    {
        && var decided_attestation_data := att_share.data;
        && var fork_version := af_bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
        && var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
        && verify_bls_signature(attestation_signing_root, att_share.signature, rs_pubkey)
    }

    predicate inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db_body(
        dvc: AttDVCState, 
        att_share: AttestationShare
    )
    {
        && var att_data: AttestationData := att_share.data;
        && var slashing_db_attestation := construct_SlashingDBAttestation_from_att_data(att_data);
        && slashing_db_attestation in dvc.attestation_slashing_db  
        && var rs_pubkey: BLSPubkey := dvc.rs.pubkey;    
        && pred_is_owner_of_att_share(rs_pubkey, att_share)
    }   

    predicate inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db(
        outputs: AttestationOutputs,
        dvc: AttDVCState)
    {
        forall att_share: AttestationShare | 
            att_share in f_get_messages_from_messages_with_recipients(outputs.att_shares_sent) 
            ::
            inv_outputs_att_shares_sent_are_tracked_in_attestation_slashing_db_body(dvc, att_share)
    } 

    predicate inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body(
        dvc: AttDVCState
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
            && pred_is_owner_of_att_share(rs_pubkey, att_share)
    }   

    predicate inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db(dv: AttDVState)
    {
        forall hn: BLSPubkey | 
            is_honest_node(dv, hn)
            ::
            inv_att_shares_to_broadcast_are_tracked_in_attestation_slashing_db_body(dv.honest_nodes_states[hn])
    } 

    predicate inv_sent_att_shares_have_corresponding_slashing_db_attestations_body(
        dvc: AttDVCState,
        att_share: AttestationShare
    )
    {
        && var att_data := att_share.data;
        && var slashing_db_attestation := construct_SlashingDBAttestation_from_att_data(att_data);
        && slashing_db_attestation in dvc.attestation_slashing_db     
    }

    predicate inv_sent_att_shares_have_corresponding_slashing_db_attestations(dv: AttDVState)
    {
        forall hn: BLSPubkey, att_share: AttestationShare | 
            && is_honest_node(dv, hn)
            && att_share in dv.att_network.allMessagesSent 
            && var dvc: AttDVCState := dv.honest_nodes_states[hn];
            && var rs_pubkey: BLSPubkey := dvc.rs.pubkey;
            && pred_is_owner_of_att_share(rs_pubkey, att_share)
            ::
            && var dvc: AttDVCState := dv.honest_nodes_states[hn];
            && inv_sent_att_shares_have_corresponding_slashing_db_attestations_body(dvc, att_share)            
    }

    predicate inv_attestation_is_created_based_on_shares_from_quorum_of_dvc_signers_helper(
        att_shares: set<AttestationShare>,
        dvc: AttDVCState
    )
    {
        exists att_share: AttestationShare ::
            && att_share in att_shares
            && var rs_pubkey := dvc.rs.pubkey;
            && pred_is_owner_of_att_share(rs_pubkey, att_share)
    }

    predicate inv_attestation_is_created_based_on_shares_from_quorum_of_dvc_signers(
        dv: AttDVState,
        att_shares: set<AttestationShare>,
        dvc_signer_pubkeys: set<BLSPubkey>
    )
    {
        forall key: BLSPubkey | key in dvc_signer_pubkeys ::
            key in dv.honest_nodes_states.Keys
            ==>
            inv_attestation_is_created_based_on_shares_from_quorum_of_dvc_signers_helper(
                    att_shares,
                    dv.honest_nodes_states[key]
                )        
    }

    predicate inv_attestation_is_created_based_on_shares_from_quorum_of_dvc_signer_pubkeys_body_helper(
        dv: AttDVState, 
        att: Attestation,
        att_shares: set<AttestationShare>, 
        signers: set<BLSPubkey>
    )
    {
        && att_shares <= dv.att_network.allMessagesSent
        && var constructed_sig := dv.construct_signed_attestation_signature(att_shares);
        && constructed_sig.isPresent()
        && constructed_sig.safe_get() == att.signature
        && all_att_shares_have_same_data(att_shares, att.data)
        && signers <= dv.all_nodes
        && inv_attestation_is_created_based_on_shares_from_quorum_of_dvc_signers(dv, att_shares, signers)
        && |signers| >= quorum(|dv.all_nodes|)
    }

    predicate inv_attestation_is_created_based_on_shares_from_quorum_of_dvc_signer_pubkeys_body(
        dv: AttDVState, 
        att: Attestation        
    )
    {
        exists att_shares, dvc_signer_pubkeys :: 
                && att_shares <= dv.att_network.allMessagesSent
                && var constructed_sig := dv.construct_signed_attestation_signature(att_shares);
                && constructed_sig.isPresent()
                && constructed_sig.safe_get() == att.signature
                && all_att_shares_have_same_data(att_shares, att.data)
                && dvc_signer_pubkeys <= dv.all_nodes
                && inv_attestation_is_created_based_on_shares_from_quorum_of_dvc_signers(dv, att_shares, dvc_signer_pubkeys)
                && |dvc_signer_pubkeys| >= quorum(|dv.all_nodes|)
    }

    predicate inv_attestation_is_created_based_on_shares_from_quorum_of_dvc_signer_pubkeys(dv: AttDVState)
    {
        forall att: Attestation | att in dv.all_attestations_created ::
                inv_attestation_is_created_based_on_shares_from_quorum_of_dvc_signer_pubkeys_body(dv, att)
    }

    predicate inv_attestation_is_created_based_shares_from_quorum_of_rs_signers_body(
        att_shares: set<AttestationShare>,
        rs_signer_pubkey: BLSPubkey
    )
    {
        exists att_share: AttestationShare ::
            && att_share in att_shares
            && pred_is_owner_of_att_share(rs_signer_pubkey, att_share)
    }

    predicate inv_attestation_is_created_based_shares_from_quorum_of_rs_signers(
        att_shares: set<AttestationShare>,
        rs_signer_pubkeys: set<BLSPubkey>
    )
    {
        forall key: BLSPubkey | key in rs_signer_pubkeys ::
                inv_attestation_is_created_based_shares_from_quorum_of_rs_signers_body(
                    att_shares,
                    key
                )        
    }

    predicate inv_outputs_attestations_submited_are_created_based_on_shares_of_quorum_body(
        dvc: AttDVCState, 
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
                && all_att_shares_have_same_data(att_shares, att.data)
                && inv_attestation_is_created_based_shares_from_quorum_of_rs_signers(att_shares, rs_signer_pubkeys)
                && |rs_signer_pubkeys| >= quorum(|dvc.peers|)
                && rs_signer_pubkeys <= dvc.peers
    }   

    predicate inv_outputs_attestations_submited_are_created_based_on_shares_of_quorum(
        outputs: AttestationOutputs,
        dvc: AttDVCState)
    {
        forall submitted_attestation | submitted_attestation in outputs.submitted_data ::
            inv_outputs_attestations_submited_are_created_based_on_shares_of_quorum_body(dvc, submitted_attestation)
    } 

    predicate inv_db_of_vp_contains_all_data_of_sent_att_shares_with_lower_slots_body(
        dv: AttDVState,
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
            && pred_is_owner_of_att_share(rs_pubkey, att_share)
            && att_share.data.slot < slot
            ::
            && var att_data := att_share.data;
            && var slashing_db_attestation := SlashingDBAttestation(
                                            source_epoch := att_data.source.epoch,
                                            target_epoch := att_data.target.epoch,
                                            signing_root := Some(hash_tree_root(att_data)));
            && slashing_db_attestation in db
    }

    predicate inv_db_of_vp_contains_all_data_of_sent_att_shares_with_lower_slots(dv: AttDVState)
    {
        forall hn: BLSPubkey, slot: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation> | 
            && is_honest_node(dv, hn) 
            && var dvc := dv.honest_nodes_states[hn];
            && slot in dvc.attestation_consensus_engine_state.slashing_db_hist
            && vp in dvc.attestation_consensus_engine_state.slashing_db_hist[slot].Keys
            && db in dvc.attestation_consensus_engine_state.slashing_db_hist[slot][vp]
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
            && pred_is_owner_of_att_share(rs_pubkey, att_share)
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
        dvc: AttDVCState        
    )
    {
        forall slot: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation> | 
            && slot in dvc.attestation_consensus_engine_state.slashing_db_hist.Keys
            && vp in dvc.attestation_consensus_engine_state.slashing_db_hist[slot].Keys
            && db in dvc.attestation_consensus_engine_state.slashing_db_hist[slot][vp]
            :: 
            inv_db_of_vp_contains_all_att_data_of_sent_att_shares_with_lower_slots_dvc_body(
                allMessagesSent,
                dvc.rs.pubkey,
                slot,
                vp,
                db
            )
    }

    predicate inv_unchanged_dvc_rs_pubkey(dv: AttDVState)
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            && var dvc: AttDVCState := dv.honest_nodes_states[hn];
            && dvc.rs.pubkey == hn
    }

    predicate inv_honest_nodes_are_not_owners_of_att_shares_from_adversary_body(
        dv: AttDVState, 
        att_share: AttestationShare
    )
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) :: 
            !pred_is_owner_of_att_share(hn, att_share)
    }

    predicate inv_honest_nodes_are_not_owners_of_att_shares_from_adversary(dv: AttDVState)
    {
        forall byz_node: BLSPubkey, att_share: AttestationShare | 
            && byz_node in dv.adversary.nodes 
            && att_share in dv.att_network.allMessagesSent
            && pred_is_owner_of_att_share(byz_node, att_share)
            ::
            inv_honest_nodes_are_not_owners_of_att_shares_from_adversary_body(dv, att_share)
    }
}