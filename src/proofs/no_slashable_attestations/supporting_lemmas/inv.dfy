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

    predicate pred_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(
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

    predicate pred_rcvd_attestation_shares_is_in_all_messages_sent_single_node(
        dv: DVState,
        n: BLSPubkey
    )
    requires n in dv.honest_nodes_states.Keys
    {
        pred_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(
            dv,
            dv.honest_nodes_states[n]
        )
    }

    predicate pred_rcvd_attestation_shares_is_in_all_messages_sent(
        dv: DVState    
    )
    {
        forall n |
            n in dv.honest_nodes_states
            ::
            pred_rcvd_attestation_shares_is_in_all_messages_sent_single_node(dv, n)
    }  

    predicate pred_4_1_b_exists(
        dv: DVState,
        hn': BLSPubkey, 
        att_share: AttestationShare,
        a: Attestation
    )
    {
        && hn' in dv.honest_nodes_states.Keys 
        && att_share in dv.att_network.allMessagesSent
        && att_share.data == a.data
        && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));
        && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
        && verify_bls_siganture(attestation_signing_root, att_share.signature, hn')
    }

    predicate pred_4_1_b(dv: DVState)
    {
        forall a |
            && a in dv.all_attestations_created
            && is_valid_attestation(a, dv.dv_pubkey)
            ::
            exists hn', att_share: AttestationShare :: pred_4_1_b_exists(dv, hn', att_share, a)
    }

    predicate pred_4_1_c(dv: DVState)
    {
        forall hn, att_share |
                && hn in dv.honest_nodes_states.Keys 
                && att_share in dv.att_network.allMessagesSent
                && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));                
                && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
                && verify_bls_siganture(attestation_signing_root, att_share.signature, hn)
            ::
                && dv.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent()
                && dv.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data
    }  

    predicate pred_4_1_f_a(dv: DVState)
    {
        forall cid |
            && cid in dv.consensus_on_attestation_data.Keys
            && dv.consensus_on_attestation_data[cid].decided_value.isPresent()
            ::
            is_a_valid_decided_value(dv.consensus_on_attestation_data[cid])
    }  


    predicate pred_4_1_f_b(dv: DVState)
    {
        forall cid |
            && cid in dv.consensus_on_attestation_data.Keys
            && dv.consensus_on_attestation_data[cid].decided_value.isPresent()
            ::
            dv.consensus_on_attestation_data[cid].decided_value.safe_get().slot == cid
    }     

    
    predicate pred_4_1_g_i_for_dvc_single_dvc(
        dv: DVState,
        n: BLSPubkey,
        cid: Slot
    )
    requires n in dv.honest_nodes_states.Keys 
    requires cid in dv.honest_nodes_states[n].attestation_consensus_engine_state.attestation_consensus_active_instances
    {
        var dvc := dv.honest_nodes_states[n];
        var acvc := dvc.attestation_consensus_engine_state.attestation_consensus_active_instances[cid];

        pred_4_1_g_i_for_dvc_single_dvc_2_body_body(
            cid, 
            acvc.attestation_duty, 
            acvc.validityPredicate
        ) 
    }

    predicate pred_4_1_g_i_for_dvc_single_dvc_2_body(
        dvc: DVCState,
        cid: Slot
    )
    requires cid in dvc.attestation_consensus_engine_state.attestation_consensus_active_instances
    {
        var acvc := dvc.attestation_consensus_engine_state.attestation_consensus_active_instances[cid];
        pred_4_1_g_i_for_dvc_single_dvc_2_body_body(
            cid, 
            acvc.attestation_duty, 
            acvc.validityPredicate
        ) 
    }     

    predicate pred_4_1_g_i_for_dvc_single_dvc_2_body_body(
        cid: Slot,
        attestation_duty: AttestationDuty,
        vp: AttestationData -> bool
    )
    {
        exists attestation_slashing_db ::
            pred_4_1_g_i_body(cid, attestation_duty, attestation_slashing_db, vp)        
    }         

    predicate pred_4_1_g_i_for_dvc_single_dvc_2(
        dvc: DVCState
    )
    {
        forall cid | 
            && cid in dvc.attestation_consensus_engine_state.attestation_consensus_active_instances
            ::
            pred_4_1_g_i_for_dvc_single_dvc_2_body(dvc, cid)        
    }    

    predicate pred_4_1_g_i_for_dvc(
        dv: DVState
    )
    {
        forall n, cid | 
            && n in dv.honest_nodes_states 
            && cid in dv.honest_nodes_states[n].attestation_consensus_engine_state.attestation_consensus_active_instances
            ::
            pred_4_1_g_i_for_dvc_single_dvc(dv, n, cid)
    }

   
    predicate pred_4_1_g_i_body(
        s: Slot,
        attestation_duty: AttestationDuty,
        attestation_slashing_db: set<SlashingDBAttestation>,
        vp: AttestationData -> bool
    )
    {
        && attestation_duty.slot == s
        && (vp == (ad: AttestationData) => consensus_is_valid_attestation_data(attestation_slashing_db, ad, attestation_duty))
    }

    predicate pred_4_1_g_i(dv: DVState)
    {
        forall hn, s: nat, vp |
            && hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
            && vp in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions[hn]
            ::
            exists attestation_duty, attestation_slashing_db ::
                pred_4_1_g_i_body(s, attestation_duty, attestation_slashing_db, vp)
    }

    predicate pred_4_1_g_ii(dv: DVState)    
    {
        forall hn, s1: nat, s2: nat, vp, db2 |
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
            && var decided_a_data := dv.consensus_on_attestation_data[s1].decided_value.safe_get();
            && var sdba := construct_SlashingDBAttestation_from_att_data(decided_a_data);
            && sdba in db2
    }    

    predicate pred_4_1_g_iii(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_g_iii_body_body(dv, dv.honest_nodes_states[hn])                
    }   

    predicate inv_g_iii_body_body(
        dv: DVState, 
        hn_state: DVCState
    ) 
    {
        forall s1: nat, s2: nat, vp, db2 |
            && s1 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
            && s2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys            
            && s1 < s2       
            && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys   
            && db2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp]           
            ::       
            inv_g_iii_body_body_body(dv, s1, db2)         
            // && dv.consensus_on_attestation_data[s1].decided_value.isPresent()
            // && var decided_a_data := dv.consensus_on_attestation_data[s1].decided_value.safe_get();
            // && var sdba := construct_SlashingDBAttestation_from_att_data(decided_a_data);
            // && sdba in db2        
    }

    predicate inv_g_iii_body_body_body(
        dv: DVState, 
        s1: nat,
        db2: set<SlashingDBAttestation>
    ) 
    {           
            && dv.consensus_on_attestation_data[s1].decided_value.isPresent()
            && var decided_a_data := dv.consensus_on_attestation_data[s1].decided_value.safe_get();
            && var sdba := construct_SlashingDBAttestation_from_att_data(decided_a_data);
            && sdba in db2        
    }    

    predicate pred_4_1_g_iii_a(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_g_iii_a_body_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn],
                dv.index_next_attestation_duty_to_be_served
            )                    
    }       

    predicate inv_g_iii_a_body_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState,
        index_next_attestation_duty_to_be_served: nat
    )
    {
        forall slot  |
            && slot in n_state.attestation_consensus_engine_state.att_slashing_db_hist
            ::
            exists i: nat :: 
                && i < index_next_attestation_duty_to_be_served
                && var an := dv.sequence_attestation_duties_to_be_served[i];
                && an.attestation_duty.slot == slot 
                && an.node == n
    }   

    predicate pred_4_1_g_iii_a_a(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_g_iii_a_a_body_body(
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

    predicate inv_g_iii_a_a_body_body(
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
    
    predicate pred_4_1_g_iii_b(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_g_iii_b_body_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn],
                dv.index_next_attestation_duty_to_be_served
            )                    
    }     

    

    predicate inv_g_iii_b_body_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState,
        index_next_attestation_duty_to_be_served: nat
    )
    {
        forall ad  |
            && ad in n_state.attestation_duties_queue
            ::
            exists i: nat :: 
                && i < index_next_attestation_duty_to_be_served
                && var an := dv.sequence_attestation_duties_to_be_served[i];
                && an.attestation_duty == ad
                && an.node == n
    }   

    

    predicate pred_4_1_g_iii_c(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_g_iii_c_body_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn],
                dv.index_next_attestation_duty_to_be_served
            )                    
    }               

    predicate inv_g_iii_c_body_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState,
        index_next_attestation_duty_to_be_served: nat
    )
    {
        n_state.latest_attestation_duty.isPresent() ==>
            exists i: nat :: 
                && i < index_next_attestation_duty_to_be_served
                && var an := dv.sequence_attestation_duties_to_be_served[i];
                && an.attestation_duty == n_state.latest_attestation_duty.safe_get()
                && an.node == n
    }     

    predicate inv_g_iii_c_new_body(  
        n: BLSPubkey,
        n_state: DVCState,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    {
        n_state.latest_attestation_duty.isPresent() ==>
            exists i: nat :: 
                && i < index_next_attestation_duty_to_be_served
                && var an := sequence_attestation_duties_to_be_served[i];
                && an.attestation_duty == n_state.latest_attestation_duty.safe_get()
                && an.node == n
    }  

    predicate inv_g_iii_b_new_body(        
        n: BLSPubkey,
        n_state: DVCState,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,    
        index_next_attestation_duty_to_be_served: nat
    )
    {
        forall ad  |
            && ad in n_state.attestation_duties_queue
            ::
            exists i: nat :: 
                && i < index_next_attestation_duty_to_be_served
                && var an := sequence_attestation_duties_to_be_served[i];
                && an.attestation_duty == ad
                && an.node == n
    }          

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

    predicate pred_4_1_g_b_new(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_g_b_body_body_new(
                dv, 
                hn,
                dv.honest_nodes_states[hn]
            )                    
    }          

    predicate inv_g_b_body_body_new(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState
    )
    {
        // n_state.latest_attestation_duty.isPresent() ==>
            forall an |
                && an in dv.sequence_attestation_duties_to_be_served.Values 
                && an.node == n 
                && an.attestation_duty.slot < get_upperlimit_decided_instances(n_state)
            ::
                var slot := an.attestation_duty.slot;
                && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in n_state.attestation_slashing_db
    }        

    predicate inv_g_d_a(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_g_d_a_body_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn]
            )                    
    }       

    predicate inv_g_d_a_body_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState
    )
    {
        forall slot |
            && slot in n_state.future_att_consensus_instances_already_decided
            ::
            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
            && n_state.future_att_consensus_instances_already_decided[slot] == dv.consensus_on_attestation_data[slot].decided_value.safe_get()
    }  

    predicate inv_g_d_b(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_g_d_b_body_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn]
            )                    
    }              

    predicate inv_g_d_b_body_body(
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

    predicate inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_head_attetation_duty_queue_higher_than_latest_attestation_duty_body_body(
                dv.honest_nodes_states[hn]
            )                    
    }                

    predicate inv_head_attetation_duty_queue_higher_than_latest_attestation_duty_body_body(
        n_state: DVCState
    )
    {
        (
            && n_state.attestation_duties_queue != []
            && n_state.latest_attestation_duty.isPresent()
        ) ==>
        n_state.attestation_duties_queue[0].slot > n_state.latest_attestation_duty.safe_get().slot     
    }

    predicate inv_attestation_duty_queue_is_ordered(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_attestation_duty_queue_is_ordered_body_body(
                dv.honest_nodes_states[hn]
            )                    
    }       

    predicate inv_attestation_duty_queue_is_ordered_body_body(
        n_state: DVCState
    )
    {
        forall i,j | 0 <= i < j < |n_state.attestation_duties_queue| :: n_state.attestation_duties_queue[i].slot <  n_state.attestation_duties_queue[j].slot           
    }

    // predicate inv_attestation_duty_queue_is_ordered_2_body_body(
    //     dv: DVState, 
    //     n: BLSPubkey,
    //     n_state: DVCState
    // )
    // {
    //     forall i, k, l, t  |
    //         && 0 < i < |n_state.attestation_duties_queue|
    //         && dv.sequence_attestation_duties_to_be_served[k].node == n
    //         && dv.sequence_attestation_duties_to_be_served[l].node == n
    //         && dv.sequence_attestation_duties_to_be_served[t].node == n
    //         && dv.sequence_attestation_duties_to_be_served[k].attestation_duty.slot == n_state.attestation_duties_queue[i-1].slot
    //         && dv.sequence_attestation_duties_to_be_served[l].attestation_duty.slot == n_state.attestation_duties_queue[i].slot
    //         ::
    //         && k < l 
    //         && !(k < t < l)

    // } 

    predicate inv_attestation_duty_queue_is_ordered_3(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_attestation_duty_queue_is_ordered_3_body_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn]            
            )                    
    }     

    predicate inv_attestation_duty_queue_is_ordered_3_body_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState
    )
    {
        forall i, k, l, t  |
            inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                dv,
                n, 
                n_state,
                i,
                k, 
                l, 
                t
            )
            ::
            n_state.attestation_duties_queue[i-1].slot == dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot

    }       

    predicate inv_attestation_duty_queue_is_ordered_3_body_body_premise(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState,
        i: nat, 
        k: nat,
        l: nat, 
        t: nat
    )
    {
            && 0 < i < |n_state.attestation_duties_queue|
            && dv.sequence_attestation_duties_to_be_served[k].node == n
            && dv.sequence_attestation_duties_to_be_served[l].node == n
            && dv.sequence_attestation_duties_to_be_served[t].node == n
            && dv.sequence_attestation_duties_to_be_served[k].attestation_duty.slot == n_state.attestation_duties_queue[i-1].slot
            && dv.sequence_attestation_duties_to_be_served[l].attestation_duty.slot == n_state.attestation_duties_queue[i].slot
            && n_state.attestation_duties_queue[i-1].slot <= dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot < dv.sequence_attestation_duties_to_be_served[l].attestation_duty.slot 
    } 
        
    predicate inv_attestation_duty_queue_is_ordered_4(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_attestation_duty_queue_is_ordered_4_body_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn],
                dv.index_next_attestation_duty_to_be_served
            )                    
    }           

    predicate inv_attestation_duty_queue_is_ordered_4_body_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState,
        index_next_attestation_duty_to_be_served: nat
    )  
    {
        |n_state.attestation_duties_queue| > 0 ==>
            forall i |
                inv_attestation_duty_queue_is_ordered_4_body_body_premise(
                    dv,
                    n, 
                    n_state,
                    i,
                    index_next_attestation_duty_to_be_served
                )
                ::
                var last := n_state.attestation_duties_queue[|n_state.attestation_duties_queue|-1];
                last.slot == dv.sequence_attestation_duties_to_be_served[i].attestation_duty.slot 

    }          

    predicate inv_attestation_duty_queue_is_ordered_4_body_body_premise(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState,
        i: nat, 
        index_next_attestation_duty_to_be_served: nat
    )
    requires |n_state.attestation_duties_queue| > 0
    {
            var last := n_state.attestation_duties_queue[|n_state.attestation_duties_queue|-1];
            && i < index_next_attestation_duty_to_be_served
            && dv.sequence_attestation_duties_to_be_served[i].node == n
            && last.slot <= dv.sequence_attestation_duties_to_be_served[i].attestation_duty.slot 
    }       
         

    predicate inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist_body_body(
                dv.honest_nodes_states[hn]
            )                    
    }       

    predicate inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist_body_body
    (
        n_state: DVCState
    )
    {
        n_state.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys <= n_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    }

    predicate inv_attestation_consensus_active_instances_predicate_is_in_att_slashing_db_hist(dv: DVState)    
    {
        forall hn, cid |
            && hn in dv.honest_nodes_states.Keys        
            ::
            inv_attestation_consensus_active_instances_predicate_is_in_att_slashing_db_hist_body(dv.honest_nodes_states[hn], cid)
             
    }       

    predicate inv_attestation_consensus_active_instances_predicate_is_in_att_slashing_db_hist_body
    (
        n_state: DVCState,
        cid: Slot
    )
    {
        && cid in n_state.attestation_consensus_engine_state.attestation_consensus_active_instances 
        ==>
        (
            && cid in n_state.attestation_consensus_engine_state.att_slashing_db_hist
            && n_state.attestation_consensus_engine_state.attestation_consensus_active_instances[cid].validityPredicate in n_state.attestation_consensus_engine_state.att_slashing_db_hist[cid] 
        )
    }    

    predicate pred_inv_current_latest_attestation_duty_match(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            pred_inv_current_latest_attestation_duty_match_body_body(
                dv.honest_nodes_states[hn]
            )                    
    }           

    predicate pred_inv_current_latest_attestation_duty_match_body_body(
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
                // && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in n_state.attestation_slashing_db
    }         

    // predicate inv_g_b_body_body(
    //     dv: DVState, 
    //     n: BLSPubkey,
    //     n_state: DVCState
    // )
    // {
    //     n_state.latest_attestation_duty.isPresent() ==>
    //         forall an |
    //             && an in dv.sequence_attestation_duties_to_be_served.Values 
    //             && an.node == n 
    //             && an.attestation_duty.slot < n_state.latest_attestation_duty.safe_get().slot
    //         ::
    //             var slot := an.attestation_duty.slot;
    //             && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
    //             && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in n_state.attestation_slashing_db
    // } 

    // predicate inv_g_a_ii_body_body(
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
    //             // && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in n_state.attestation_slashing_db
    // }    

    predicate inv_g_a_ii_a(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_g_a_ii_a_body_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn]
            )                    
    }       

    predicate inv_g_a_ii_a_body_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState
    )
    {
        (
            &&  |n_state.attestation_duties_queue| > 0 
            &&   !n_state.current_attestation_duty.isPresent()
        )
        ==>
            forall an |
                && an in dv.sequence_attestation_duties_to_be_served.Values 
                && an.node == n 
                && an.attestation_duty.slot < n_state.attestation_duties_queue[0].slot
            ::
                var slot := an.attestation_duty.slot;
                && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in n_state.attestation_slashing_db
    }     

    predicate inv_g_a_iii(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_g_a_iii_body_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn],
                dv.index_next_attestation_duty_to_be_served
            )                    
    }  

    predicate inv_g_a_iii_body_body_helper(
        n_state: DVCState,
        slot: nat
    ) 
    {
        n_state.current_attestation_duty.isPresent() ==>
            slot != n_state.current_attestation_duty.safe_get().slot
    }    

    predicate inv_g_a_iii_body_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState,
        index_next_attestation_duty_to_be_served: nat
    )
    {
        (
            &&  |n_state.attestation_duties_queue| == 0 
            // &&   !n_state.current_attestation_duty.isPresent()
        ) ==>
            forall i:nat  |
                && i < index_next_attestation_duty_to_be_served
                && var an := dv.sequence_attestation_duties_to_be_served[i];
                && an.node == n 
                && inv_g_a_iii_body_body_helper(n_state, an.attestation_duty.slot)
                ::
                && var an := dv.sequence_attestation_duties_to_be_served[i];
                var slot := an.attestation_duty.slot;
                && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in n_state.attestation_slashing_db
    }  

    predicate inv_g_a_iii_b_body_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState,
        index_next_attestation_duty_to_be_served: nat
    )
    {
        (
            &&  |n_state.attestation_duties_queue| == 0 
            &&   n_state.current_attestation_duty.isPresent()
        ) ==>
            forall i:nat  |
                && i < index_next_attestation_duty_to_be_served
                && var an := dv.sequence_attestation_duties_to_be_served[i];
                && an.node == n 
                // && an.attestation_duty
                ::
                && var an := dv.sequence_attestation_duties_to_be_served[i];
                var slot := an.attestation_duty.slot;
                && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in n_state.attestation_slashing_db
    }      

    predicate inv_g_a_iv_a(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_g_a_iv_a_body_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn]
            )                    
    }     

    predicate inv_g_a_iv_a_body_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState
    )
    {
        (
            &&  |n_state.attestation_duties_queue| > 0 
            &&   n_state.latest_attestation_duty.isPresent()
        )
        ==>
            forall an |
                && an in dv.sequence_attestation_duties_to_be_served.Values 
                && an.node == n 
                && n_state.latest_attestation_duty.safe_get().slot < an.attestation_duty.slot < n_state.attestation_duties_queue[0].slot
            ::
                var slot := an.attestation_duty.slot;
                && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in n_state.attestation_slashing_db
    }                  



    predicate inv_g_c(dv: DVState)
    {
        forall n | n in dv.honest_nodes_states.Keys :: inv_g_c_body(dv, n)
    }    

    predicate inv_g_c_body(
        dv: DVState, 
        n: BLSPubkey
    )
    requires n in dv.honest_nodes_states.Keys 
    {
        var n_state := dv.honest_nodes_states[n];
        inv_g_c_body_body(dv, n, n_state, dv.index_next_attestation_duty_to_be_served)
    }

    predicate inv_g_c_body_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState,
        index_next_attestation_duty_to_be_served: nat
    )
    {
        n_state.latest_attestation_duty.isPresent() ==>
            forall i:nat  |
                && i < index_next_attestation_duty_to_be_served
                && var an := dv.sequence_attestation_duties_to_be_served[i];
                && an in dv.sequence_attestation_duties_to_be_served.Values 
                && an.node == n 
                && an.attestation_duty.slot > n_state.latest_attestation_duty.safe_get().slot 
                && !dv.consensus_on_attestation_data[an.attestation_duty.slot].decided_value.isPresent()
                ::
                && var an := dv.sequence_attestation_duties_to_be_served[i];
                an.attestation_duty in n_state.attestation_duties_queue
    }    

    predicate inv_g_c_ii_body_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState,
        index_next_attestation_duty_to_be_served: nat
    )
    {
        !n_state.latest_attestation_duty.isPresent() ==>
            forall i:nat  |
                && i < index_next_attestation_duty_to_be_served
                && var an := dv.sequence_attestation_duties_to_be_served[i];
                && an in dv.sequence_attestation_duties_to_be_served.Values 
                && an.node == n 
                && !dv.consensus_on_attestation_data[an.attestation_duty.slot].decided_value.isPresent()
                ::
                && var an := dv.sequence_attestation_duties_to_be_served[i];
                an.attestation_duty in n_state.attestation_duties_queue
    }    


    predicate inv_g_d_body_body(
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


    

    predicate inv47_body(dv: DVState, hn: BLSPubkey, s: Slot)
    {
        && is_honest_node(dv, hn)
        && var hn_state := dv.honest_nodes_states[hn];
        && ( s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                    ==> (exists duty: AttestationDuty :: duty in hn_state.all_rcvd_duties && duty.slot == s)
           )
    }

    predicate inv47(dv: DVState)
    {
        forall hn: BLSPubkey, s: Slot | is_honest_node(dv, hn) ::
            inv47_body(dv, hn, s)
    }  

    predicate inv43_body_a(dv: DVState, hn: BLSPubkey, s: Slot)
    requires is_honest_node(dv, hn)
    requires s in dv.consensus_on_attestation_data.Keys         
    requires hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys      
    requires && inv47_body(dv, hn, s) 
             && inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv) 
    // requires && var hn_state := dv.honest_nodes_states[hn];
    //          && exists duty: AttestationDuty :: duty in hn_state.all_rcvd_duties && duty.slot == s    
    {    
        && var hn_state := dv.honest_nodes_states[hn];        
        && var duty: AttestationDuty :| duty in hn_state.all_rcvd_duties && duty.slot == s;        
        && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys                
        && (forall vp, db |
                && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s].Keys 
                && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
                ::
                && db <= hn_state.attestation_slashing_db                    
           )        
    }

    predicate inv43_body_b(dv: DVState, hn: BLSPubkey, s: Slot, 
                            ci: ConsensusInstance<AttestationData>, h_nodes: set<BLSPubkey>)
    requires is_honest_node(dv, hn)
    requires s in dv.consensus_on_attestation_data.Keys         
    requires hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys      
    // requires && var hn_state := dv.honest_nodes_states[hn];
    //         && exists duty: AttestationDuty :: duty in hn_state.all_rcvd_duties && duty.slot == s
    requires && inv47_body(dv, hn, s) 
             && inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv)     
    requires s in dv.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys                
    requires is_a_valid_decided_value_according_to_set_of_nodes(ci, h_nodes)
    {
        && var hn_state := dv.honest_nodes_states[hn];        
        && var duty: AttestationDuty :| duty in hn_state.all_rcvd_duties && duty.slot == s;        
        && ( && dv.consensus_on_attestation_data[s].decided_value.isPresent()
             && hn in h_nodes
                    ==> && var ad := dv.consensus_on_attestation_data[s].decided_value.safe_get();
                        && exists vp, db :: 
                                        && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s].Keys 
                                        && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
                                        && consensus_is_valid_attestation_data(db, ad, duty)    
           )
    }

    predicate inv43(dv: DVState)
    {
        forall hn: BLSPubkey, s: Slot |            
            && is_honest_node(dv, hn)
            && var hn_state := dv.honest_nodes_states[hn];
            && s in dv.consensus_on_attestation_data.Keys
            && hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys      
            // && exists duty: AttestationDuty :: duty in hn_state.all_rcvd_duties && duty.slot == s            
            && inv47_body(dv, hn, s) 
            && inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv)           
            ::            
            && inv43_body_a(dv, hn, s)
            && ( dv.consensus_on_attestation_data[s].decided_value.isPresent() 
                    ==> exists h_nodes :: && is_a_valid_decided_value_according_to_set_of_nodes(
                                                dv.consensus_on_attestation_data[s], 
                                                h_nodes) 
                                          && inv43_body_b(dv, hn, s, dv.consensus_on_attestation_data[s], h_nodes)
               )                          
    }   

    predicate has_all_slashing_db_attestations_before_slot_s(
        db: set<SlashingDBAttestation>,
        S: set<SlashingDBAttestation>,
        s: Slot
    )
    requires (forall r: SlashingDBAttestation :: 
                    r in db ==> (exists data: AttestationData :: r.signing_root == Some(hash_tree_root(data))))
    {
        && S <= db
        && forall r | r in db && r !in S :: get_slot_from_slashing_db_attestation(r) >= s
        && forall r | r in S :: get_slot_from_slashing_db_attestation(r) < s
    }

    predicate inv44_body(dv: DVState, hn: BLSPubkey, s1: Slot, s2: Slot, vp1: AttestationData -> bool, vp2: AttestationData -> bool, db2: set<SlashingDBAttestation>)
    requires is_honest_node(dv, hn)
    requires && var hn_state: DVCState := dv.honest_nodes_states[hn];
             && s1 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
             && s2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
             && s1 < s2
             && vp1 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s1].Keys
             && vp2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys
    requires && var hn_state: DVCState := dv.honest_nodes_states[hn];
            && ( forall db, r: SlashingDBAttestation |
                    && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s1][vp1]
                    && r in db
                    :: 
                        (exists data: AttestationData :: r.signing_root == Some(hash_tree_root(data))) )
    {
        forall T |
        && var hn_state: DVCState := dv.honest_nodes_states[hn];
        && T in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s1][vp1]
        ::
        && var db1: set<SlashingDBAttestation> :| has_all_slashing_db_attestations_before_slot_s(T, db1, s2);
        && db1 <= db2   
    }
    predicate inv44(dv: DVState)
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            && var hn_state := dv.honest_nodes_states[hn];
            && forall s1: Slot, s2: Slot, vp1, vp2, db2 |
                    && s1 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                    && s2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
                    && s1 < s2
                    && vp1 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s1].Keys
                    && vp2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys
                    && db2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp2]
                    && ( forall db, r: SlashingDBAttestation |
                            && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s1][vp1]
                            && r in db
                            :: 
                                (exists data: AttestationData :: r.signing_root == Some(hash_tree_root(data))) )
                    ::
                    inv44_body(dv, hn, s1, s2, vp1, vp2, db2)
                    
    }  


    predicate inv45(dv: DVState)
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            && var hn_state := dv.honest_nodes_states[hn];
            && forall s: Slot, vp, db | 
                && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s]
                && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
                ::
                    db <= hn_state.attestation_slashing_db
    }  

    predicate inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv: DVState)
    {
        forall hn: BLSPubkey, s: Slot | is_honest_node(dv, hn) ::
            && var hn_state := dv.honest_nodes_states[hn];
            && ( hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
                    ==> s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys)
    }

    predicate inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body(
        dv: DVState, 
        hn: BLSPubkey,
        hn_state: DVCState,
        s: Slot,
        vp: AttestationData -> bool
    )
    requires hn in dv.honest_nodes_states
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
            vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s]   
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

    // For every consensus instance ci, ci.decided value.isP resent() 
    // if and only if is a valid decided value(ci).
    predicate inv41<D(!new, 0)>(ci: ConsensusInstance<D>)
    {
        ci.decided_value.isPresent()
            <==> is_a_valid_decided_value(ci)            
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
    
    


    

    predicate pred_4_1_witness(
        dv: DVState, a: Attestation, a': Attestation, m: BLSPubkey,
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


    predicate inv49(dv: DVState)
    {
        forall hn: BLSPubkey, d1: AttestationDuty, d2: AttestationDuty | 
            && is_honest_node(dv, hn)
            && var hn_state := dv.honest_nodes_states[hn];
            && d1 in hn_state.all_rcvd_duties
            && d2 in hn_state.all_rcvd_duties
            && d1.slot == d2.slot
            ::
            d1 == d2
    }

    predicate inv50_body(dv: DVState, hn: BLSPubkey, s: Slot, 
                            db: set<SlashingDBAttestation>, duty: AttestationDuty, vp: AttestationData -> bool)
    requires && is_honest_node(dv, hn)
             && var hn_state := dv.honest_nodes_states[hn];
             && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
             && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s]
             // && duty in hn_state.all_rcvd_duties
             // && duty.slot == s
    {
        && var hn_state := dv.honest_nodes_states[hn];
        && duty.slot == s
        && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
        && vp == (ad: AttestationData) => consensus_is_valid_attestation_data(db, ad, duty)
    }
    predicate inv50(dv: DVState)
    {
        forall hn: BLSPubkey, s: Slot, vp: AttestationData -> bool | 
            && is_honest_node(dv, hn)
            && var hn_state := dv.honest_nodes_states[hn];
            && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
            && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s]
            ::
            exists duty, db ::
                && var hn_state := dv.honest_nodes_states[hn];
                && inv50_body(dv, hn, s, db, duty, vp)
    }

    

    predicate inv48_body(dv: DVState, s: Slot, hn: BLSPubkey) 
    {
        && var ci := dv.consensus_on_attestation_data[s];
        && hn in ci.honest_nodes_validity_functions.Keys
        && ci.honest_nodes_validity_functions[hn] != {}                
    }
    
    predicate inv48(dv: DVState)
    {
        forall s: Slot ::
            && var ci := dv.consensus_on_attestation_data[s];
            && ( ci.decided_value.isPresent()
                    <==> ( exists h_nodes :: 
                                && is_a_valid_decided_value_according_to_set_of_nodes(ci, h_nodes)            
                                && ( forall hn: BLSPubkey :: 
                                            && is_honest_node(dv, hn)
                                            && hn in h_nodes
                                                    ==> inv48_body(dv, s, hn)                                        
                                   )
                         )
                              
               )
    }


    predicate inv53(dv: DVState)
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

    predicate inv_unchanged_honesty(dv: DVState)
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
        forall n | n in dv.honest_nodes_states.Keys :: 
            var nodes := dv.honest_nodes_states[n];
            && nodes.construct_signed_attestation_signature == dv.construct_signed_attestation_signature
            && nodes.dv_pubkey == dv.dv_pubkey       
            && nodes.peers == dv.all_nodes
    }

    predicate old_inv4_body(dv: DVState, n: BLSPubkey, dvc: DVCState)    
    requires n in dv.honest_nodes_states.Keys
    requires dvc == dv.honest_nodes_states[n]
    {
        forall duty: AttestationDuty | duty in dvc.all_rcvd_duties ::
                exists k: nat :: 
                    && 0 <= k < dv.index_next_attestation_duty_to_be_served
                    && dv.sequence_attestation_duties_to_be_served[k].node == n
                    && dv.sequence_attestation_duties_to_be_served[k].attestation_duty == duty
    }

    predicate old_inv4(dv: DVState)
    {
        forall n: BLSPubkey | n in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[n];
            && old_inv4_body(dv, n, dvc)
    }


    predicate inv4_body(
        hn: BLSPubkey, 
        all_rcvd_duties: set<AttestationDuty>, 
        seq_att_duties: iseq<AttestationDutyAndNode>,
        len: nat
    )    
    {
        forall duty: AttestationDuty | duty in all_rcvd_duties ::
            exists k: nat :: 
                && 0 <= k < len
                && seq_att_duties[k].node == hn
                && seq_att_duties[k].attestation_duty == duty
    }

    predicate inv4(dv: DVState)
    {
        forall n: BLSPubkey | n in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[n];
            && inv4_body(
                    n, 
                    dvc.all_rcvd_duties, 
                    dv.sequence_attestation_duties_to_be_served,
                    dv.index_next_attestation_duty_to_be_served)
    }

    predicate inv5_body(dvc: DVCState)
    {
        forall k: nat ::
            0 <= k < |dvc.attestation_duties_queue|
                ==> ( && var queued_duty: AttestationDuty := dvc.attestation_duties_queue[k];
                      && queued_duty in dvc.all_rcvd_duties )
    }

    predicate inv5(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv5_body(dvc)
    }

    predicate inv6_body(dvc: DVCState)
    {
        dvc.current_attestation_duty.isPresent()
            ==> dvc.current_attestation_duty.safe_get()
                    in dvc.all_rcvd_duties
    }

    predicate inv6(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv6_body(dvc)
    }

    predicate inv7_body(dvc: DVCState)
    {
        dvc.latest_attestation_duty.isPresent()
            ==> dvc.latest_attestation_duty.safe_get()
                    in dvc.all_rcvd_duties
    }

    predicate inv7(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv7_body(dvc)
    }

    predicate inv8_body(dvc: DVCState)
    {
        !dvc.latest_attestation_duty.isPresent()
            ==> !dvc.current_attestation_duty.isPresent()
    }

    predicate inv8(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv8_body(dvc)
    }
  
    predicate inv9_body(dvc: DVCState)
    {
        !dvc.latest_attestation_duty.isPresent()
            ==> ( || !dvc.current_attestation_duty.isPresent()
                  || ( && dvc.latest_attestation_duty.isPresent()
                       && dvc.current_attestation_duty.isPresent()
                       && dvc.current_attestation_duty.safe_get()
                                == dvc.latest_attestation_duty.safe_get()
                     )
                )
    }

    predicate inv9(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv9_body(dvc)
    }

    predicate inv10_body(dvc: DVCState)
    {
        dvc.current_attestation_duty.isPresent()
            ==> ( && dvc.latest_attestation_duty.isPresent()
                  && dvc.current_attestation_duty.safe_get()
                                == dvc.latest_attestation_duty.safe_get()                   
                )
    }

    predicate inv10(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv10_body(dvc)
    }

    predicate inv11_body(dvc: DVCState, next_duty: AttestationDuty)
    {
        dvc.current_attestation_duty.isPresent()
            ==> dvc.current_attestation_duty.safe_get().slot < next_duty.slot        
    }

    predicate inv11(dv: DVState)
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
            && inv11_body(dvc, next_duty)
    }

    predicate inv12_body(dvc: DVCState, next_duty: AttestationDuty)
    {
        dvc.latest_attestation_duty.isPresent()
            ==> dvc.latest_attestation_duty.safe_get().slot < next_duty.slot        
    }

    predicate inv12(dv: DVState)
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
            && inv12_body(dvc, next_duty)
    }

    predicate inv13(dv: DVState)
    {
        is_sequence_attestation_duties_to_be_served_orderd(dv)
    }

    predicate inv14_body(dvc: DVCState, next_duty: AttestationDuty)
    {
       forall rcvd_duty: AttestationDuty | rcvd_duty in dvc.all_rcvd_duties ::
            rcvd_duty.slot < next_duty.slot        
    }

    predicate inv14(dv: DVState)
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
            && inv14_body(dvc, next_duty)
    }

    predicate inv15_body(dvc: DVCState, next_duty: AttestationDuty)
    {
       forall rcvd_duty: AttestationDuty | rcvd_duty in dvc.attestation_duties_queue ::
            rcvd_duty.slot < next_duty.slot        
    }

    predicate inv15(dv: DVState)
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
            && inv15_body(dvc, next_duty)
    }

    predicate inv16_body(dvc: DVCState)
    {
        !dvc.latest_attestation_duty.isPresent()
            ==> |dvc.attestation_duties_queue| == 0
    }

    predicate inv16(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv16_body(dvc)
    }

    predicate inv17_body(dvc: DVCState)
    {
        && var queue := dvc.attestation_duties_queue;
        && ( forall k1: nat, k2: nat |
                &&  0 <= k1
                &&  k1 < k2
                &&  k2 < |queue|
                ::
                    queue[k1].slot < queue[k2].slot
           )
    }

    predicate inv17(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv17_body(dvc)
    }

    predicate inv18_body(dvc: DVCState)
    {
        && var queue := dvc.attestation_duties_queue;
        && dvc.latest_attestation_duty.isPresent()
        ==>
        && ( forall k: nat |
                &&  0 <= k
                &&  k < |queue|                
                ::
                dvc.latest_attestation_duty.safe_get().slot < queue[k].slot 
           )
    }

    predicate inv18(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv18_body(dvc)
    }

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

    predicate inv19(dv: DVState)
    {        
        && ( forall k1: nat, k2: nat ::
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

    predicate inv20(dv: DVState, dv': DVState)
    {
        dv.sequence_attestation_duties_to_be_served
                == dv'.sequence_attestation_duties_to_be_served
    }

    predicate inv21_body(dvc: DVCState, duty: AttestationDuty)
    {
        duty in dvc.all_rcvd_duties
    }

    predicate inv21(dv: DVState)
    {
        forall k: nat ::
            && 0 <= k < dv.index_next_attestation_duty_to_be_served
            && dv.sequence_attestation_duties_to_be_served[k].node in dv.honest_nodes_states.Keys
            ==> 
            && var duty_and_node: AttestationDutyAndNode := dv.sequence_attestation_duties_to_be_served[k];
            && var duty := duty_and_node.attestation_duty;
            && var hn := duty_and_node.node;
            && var dvc := dv.honest_nodes_states[hn];
            && inv21_body(dvc, duty)
    }    

    predicate inv22_body(dvc: DVCState)
    {
        !dvc.latest_attestation_duty.isPresent()
            ==> dvc.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys == {}
    }

    predicate inv22(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv22_body(dvc)
    }
    
    predicate inv23_body(dvc: DVCState)
    {
        dvc.latest_attestation_duty.isPresent()
        ==> ( forall k: Slot | k in dvc.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys 
                ::
                k <= dvc.latest_attestation_duty.safe_get().slot
            )
    }

    predicate inv23(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv23_body(dvc)
    }

    predicate inv24_body(dvc: DVCState)
    {
        dvc.latest_attestation_duty.isPresent()
        ==> ( forall k: Slot, n: nat | 
                && k in dvc.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys 
                && 0 <= n < |dvc.attestation_duties_queue|
                ::
                k <= dvc.attestation_duties_queue[n].slot
            )
    }

    predicate inv24(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv24_body(dvc)
    }

    predicate inv25_body(dvc: DVCState)
    {
        forall k: Slot | k in dvc.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys ::
            exists rcvd_duty: AttestationDuty :: 
                && rcvd_duty in dvc.all_rcvd_duties
                && rcvd_duty.slot == k
    }

    predicate inv25(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv25_body(dvc)
    }

    predicate inv26_body(dvc: DVCState)
    {
        forall k: Slot | k in dvc.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys 
            ::
            && dvc.attestation_consensus_engine_state.attestation_consensus_active_instances[k].attestation_duty
                    in dvc.all_rcvd_duties                
            && dvc.attestation_consensus_engine_state.attestation_consensus_active_instances[k].attestation_duty.slot == k
    }

    predicate inv26(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv26_body(dvc)
    }

    predicate inv51_body(hn_state: DVCState, s: Slot)
    requires s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    {
        exists duty: AttestationDuty :: 
                    && duty in hn_state.all_rcvd_duties
                    && duty.slot == s
    }


    predicate inv51(dv: DVState)
    {
        forall hn: BLSPubkey, s: Slot ::
            ( && is_honest_node(dv, hn) 
              && var hn_state := dv.honest_nodes_states[hn];
              && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
            )
            ==>
            inv51_body(dv.honest_nodes_states[hn], s)                
    }

    predicate inv27_body(hn_state: DVCState)    
    {
        forall k: Slot | k in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys ::
            exists duty: AttestationDuty :: 
                    && duty in hn_state.all_rcvd_duties
                    && duty.slot == k
    }

    predicate inv27(dv: DVState)
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            && var hn_state := dv.honest_nodes_states[hn];            
            && inv27_body(hn_state)       
    }

    predicate inv28_body_ces(ces: ConsensusEngineState)
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

    predicate inv28_body(hn_state: DVCState)
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

    predicate inv28(dv: DVState)
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv28_body(dvc)
    }

    predicate inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(hn_state: DVCState)
    {
        forall k: Slot |
            k in hn_state.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys ::
                && var ci := hn_state.attestation_consensus_engine_state.attestation_consensus_active_instances[k];
                && var vp: AttestationData -> bool := ci.validityPredicate;
                && k in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
                && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[k].Keys             
    }

    predicate inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k(dv: DVState)
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(dvc)
    }

    predicate inv_monotonic_att_slashing_db_body(dvc: DVCState, dvc': DVCState)
    {
        dvc.attestation_slashing_db <= dvc'.attestation_slashing_db
    }

    predicate inv_monotonic_att_slashing_db(dv: DVState, event: DV.Event, dv': DVState)    
    // requires NextEventPreCond(dv, event)
    // requires NextEvent(dv, event, dv')    
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
    // requires NextEventPreCond(dv, event)
    // requires NextEvent(dv, event, dv')    
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            && hn in dv'.honest_nodes_states
            && var dvc := dv.honest_nodes_states[hn];
            && var dvc' := dv'.honest_nodes_states[hn];
            && inv_monotonic_att_slashing_db_hist_body(dvc, dvc')
    }

    predicate inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper_body(dv: DVState, hn: BLSPubkey)
    {
        hn in dv.honest_nodes_states.Keys        
            ==> && var hn_state := dv.honest_nodes_states[hn];
                && forall s: Slot ::
                        ( hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
                            ==> s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                        )
    }

    predicate inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper(dv: DVState)
    {
        forall hn: BLSPubkey :: inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper_body(dv, hn)        
    }

    predicate prop_monotonic_set_of_in_transit_messages(dv: DVState, dv': DVState)
    {
        && dv.att_network.allMessagesSent <= dv'.att_network.allMessagesSent
    }
     
   
    predicate inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_body(dvc: DVCState)
    {
        dvc.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys 
        <= 
        dvc.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    } 

    predicate inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist(dv: DVState)
    {
        forall hn | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_active_attn_consensus_instances_are_trackedin_att_slashing_db_hist_body(dvc)
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

    // Received attestation shares are from sent messages.
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

    // For every honest DVC, its attestation shares to broadcast is a subset of a set of sent messages in DV. 
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

    
}