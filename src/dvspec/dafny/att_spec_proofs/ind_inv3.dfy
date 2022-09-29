include "../commons.dfy"
include "../att_spec_proofs/helper_sets_lemmas.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "dvn_next_inv.dfy"
include "ind_inv.dfy"
include "ind_inv2.dfy"

module IndInv3
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV    
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Helper_Sets_Lemmas
    import opened DVN_Next_Inv
    import opened Att_Ind_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Att_Ind_Inv_With_Empty_Initial_Attestation_Slashing_DB2

    predicate inv33_body(
        dvn: DVState, 
        hn: BLSPubkey,
        hn_state: DVCNodeState,
        s: Slot
    )
    {
                ( hn in dvn.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
                    ==> s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                )
    }

    predicate inv33(dvn: DVState)
    {
        forall hn: BLSPubkey, s: Slot |
            hn in dvn.honest_nodes_states
            :: 
            inv33_body(dvn, hn, dvn.honest_nodes_states[hn], s)        
    }  

    lemma lemma_att_slashing_db_hist_is_monotonic_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        s': DVCNodeState
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state  
    ensures process.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
    {
        var s_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );
        lemma_att_slashing_db_hist_is_monotonic_f_check_for_next_queued_duty(s_mod, s');        
    }       

    lemma lemma_att_slashing_db_hist_is_monotonic_f_att_consensus_decided(
        s: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCNodeState
    )
    requires f_att_consensus_decided.requires(s, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(s, id, decided_attestation_data).state
    ensures s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;   
    {
        var local_current_attestation_duty := s.current_attestation_duty.safe_get();
        var attestation_slashing_db := f_update_attestation_slashing_db(s.attestation_slashing_db, decided_attestation_data);

        var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
        var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
        var attestation_signature_share := rs_sign_attestation(decided_attestation_data, fork_version, attestation_signing_root, s.rs);
        var attestation_with_signature_share := AttestationShare(
                aggregation_bits := get_aggregation_bits(local_current_attestation_duty.validator_index),
                data := decided_attestation_data, 
                signature := attestation_signature_share
            ); 

        var s := 
            s.(
                current_attestation_duty := None,
                attestation_shares_to_broadcast := s.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                attestation_slashing_db := attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    s.attestation_consensus_engine_state,
                    attestation_slashing_db
                )
            );

        lemma_att_slashing_db_hist_is_monotonic_f_check_for_next_queued_duty(s, s');             
    }     

    lemma lemma_att_slashing_db_hist_is_monotonic_f_listen_for_new_imported_blocks(
        s: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState
    )
    requires f_listen_for_new_imported_blocks.requires(s, block)
    requires s' == f_listen_for_new_imported_blocks(s, block).state
    ensures s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys; 
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(s, block);

        var att_consensus_instances_already_decided := s.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(s, att_consensus_instances_already_decided);

        var s :=
                s.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    s.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := s.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := s.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );                     

        if s.current_attestation_duty.isPresent() && s.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            // Stop(current_attestation_duty.safe_get().slot);
            var decided_attestation_data := att_consensus_instances_already_decided[s.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(s.attestation_slashing_db, decided_attestation_data);
            var s := s.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    s.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );
            assert s' == f_check_for_next_queued_duty(s).state;
            lemma_att_slashing_db_hist_is_monotonic_f_check_for_next_queued_duty(s, s');
        }
    }      

    lemma lemma_att_slashing_db_hist_is_monotonic_f_check_for_next_queued_duty(
        s: DVCNodeState,
        s': DVCNodeState
    )
    requires f_check_for_next_queued_duty.requires(s)
    requires s' == f_check_for_next_queued_duty(s).state
    ensures s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
    decreases s.attestation_duties_queue
    {
        if  && s.attestation_duties_queue != [] 
            && (
                || s.attestation_duties_queue[0].slot in s.future_att_consensus_instances_already_decided
                || !s.current_attestation_duty.isPresent()
            )    
        {
            
            if s.attestation_duties_queue[0].slot in s.future_att_consensus_instances_already_decided.Keys 
            {
                var queue_head := s.attestation_duties_queue[0];
                var new_attestation_slashing_db := f_update_attestation_slashing_db(s.attestation_slashing_db, s.future_att_consensus_instances_already_decided[queue_head.slot]);
                var s_mod := s.(
                    attestation_duties_queue := s.attestation_duties_queue[1..],
                    future_att_consensus_instances_already_decided := s.future_att_consensus_instances_already_decided - {queue_head.slot},
                    attestation_slashing_db := new_attestation_slashing_db,
                    attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                        s.attestation_consensus_engine_state,
                        new_attestation_slashing_db
                    )                        
                );
                lemma_pred_4_1_g_iii_f_check_for_next_queued_duty_updateConsensusInstanceValidityCheck(
                    s.attestation_consensus_engine_state,
                    new_attestation_slashing_db,
                    s_mod.attestation_consensus_engine_state
                );
                assert s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                lemma_att_slashing_db_hist_is_monotonic_f_check_for_next_queued_duty(s_mod, s');
            }
            else
            {

            }
        }
    }      

    lemma lemma_att_slashing_db_hist_is_monotonic(
        s: DVCNodeState,
        event: Types.Event,
        s': DVCNodeState,
        outputs: Outputs        
    )
    requires DVCNode_Spec.Next(s, event, s', outputs)
    ensures s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
    {
        match event
        {
            case ServeAttstationDuty(attestation_duty) => 
                lemma_att_slashing_db_hist_is_monotonic_f_serve_attestation_duty(s, attestation_duty, s');

            case AttConsensusDecided(id, decided_attestation_data) => 
                lemma_att_slashing_db_hist_is_monotonic_f_att_consensus_decided(s, id, decided_attestation_data, s');
            
            case ReceviedAttesttionShare(attestation_share) => 
                assert s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;

            case ImportedNewBlock(block) => 
                lemma_att_slashing_db_hist_is_monotonic_f_listen_for_new_imported_blocks(s, block, s');
            
            case ResendAttestationShares => 
                assert s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
        
            case NoEvent => 
                assert s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;

        }        
    }

    lemma lemma_inv_33_helper(
        s: DVState,
        event: DV.Event,
        cid: Slot,
        hn: BLSPubkey,
        s': DVState
    )
    requires NextEvent(s, event, s')
    requires inv1(s)
    requires inv53(s)
    requires inv3(s)    
    requires hn in s.honest_nodes_states.Keys
    requires inv33_body(s, hn, s.honest_nodes_states[hn], cid)
    requires inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(s)
    ensures inv33_body(s', hn, s'.honest_nodes_states[hn], cid)
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>

                var s_w_honest_node_states_updated := lemma_pred_4_1_f_g_i_get_s_w_honest_node_states_updated(s, node, nodeEvent);           

                assert s_w_honest_node_states_updated.consensus_on_attestation_data == s.consensus_on_attestation_data;


                var output := 
                    if nodeEvent.AttConsensusDecided? && nodeEvent.id == cid then 
                        Some(Decided(node, nodeEvent.decided_attestation_data))
                    else
                        None
                    ;

                var validityPredicates := 
                    map n |
                            && n in s_w_honest_node_states_updated.honest_nodes_states.Keys 
                            && cid in s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.attestation_consensus_active_instances.Keys
                        ::
                            s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.attestation_consensus_active_instances[cid].validityPredicate
                    ;

                var s_consensus := s_w_honest_node_states_updated.consensus_on_attestation_data[cid];
                var s'_consensus := s'.consensus_on_attestation_data[cid];                

                assert
                    ConsensusSpec.Next(
                        s_consensus,
                        validityPredicates,
                        s'_consensus,
                        output
                    );
                   
                if  hn in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions.Keys  
                {
                    if hn in  s.consensus_on_attestation_data[cid].honest_nodes_validity_functions.Keys
                    {
                        assert inv33_body(s, hn, s.honest_nodes_states[hn], cid);

                        assert cid in s.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                    }
                    else 
                    {
                        assert hn in validityPredicates;
                        assert cid in s.honest_nodes_states[hn].attestation_consensus_engine_state.attestation_consensus_active_instances.Keys;
                        assert inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist_body_body(s.honest_nodes_states[hn]);
                        assert cid in s.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                    }

                    if hn == node 
                    {
                        assert DVCNode_Spec.Next(s_w_honest_node_states_updated.honest_nodes_states[hn], nodeEvent, s'.honest_nodes_states[hn], nodeOutputs);
                        lemma_att_slashing_db_hist_is_monotonic(s_w_honest_node_states_updated.honest_nodes_states[hn], nodeEvent, s'.honest_nodes_states[hn], nodeOutputs);
                        assert s_w_honest_node_states_updated.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                        assert cid in s'.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                    }
                    else 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        assert cid in s'.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                    }
                }  

                         
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) => 
                assert s'.consensus_on_attestation_data == s.consensus_on_attestation_data;
                assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                 
                if
                    && hn in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions.Keys
                {
                    assert inv33_body(s, hn, s.honest_nodes_states[hn], cid);
                    assert cid in s.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                    assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                    assert cid in s'.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys;                    
                } 

        }
    }   

    lemma lemma_inv_33(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEvent(s, event, s')
    requires inv1(s)
    requires inv53(s)
    requires inv3(s)    
    requires inv33(s)   
    requires inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(s)
    ensures inv33(s')   
    {
        forall hn: BLSPubkey, slot: Slot |
            hn in s'.honest_nodes_states
        ensures inv33_body(s', hn, s'.honest_nodes_states[hn], slot)    
        {
            lemma_inv_33_helper(s, event, slot, hn, s');
        }
    }  

    lemma lemma_inv33_implies_46_a(dvn: DVState)
    requires inv33(dvn)
    ensures inv46_a(dvn)
    {
        forall hn: BLSPubkey, s: Slot | is_honest_node(dvn, hn)
        ensures
                var hn_state := dvn.honest_nodes_states[hn];
                && ( hn in dvn.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
                    ==> s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys)
                ;        
        {
            assert hn in dvn.honest_nodes_states.Keys;
            var hn_state := dvn.honest_nodes_states[hn];
            assert inv33_body(dvn, hn, hn_state, s);
            assert
                && ( hn in dvn.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
                    ==> s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys)
                ;
        }
    }  

    lemma lemma_inv_46_a(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEvent(s, event, s')
    requires inv1(s)
    requires inv53(s)
    requires inv3(s)   
    requires inv33(s)   
    requires inv46_a(s)   
    requires inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(s)
    ensures inv46_a(s')   
    {
        lemma_inv_33(s, event, s');
        lemma_inv33_implies_46_a(s');
    }     

    lemma lemma_add_set_of_validity_predicates<D(!new, 0)>(
        existing_honest_nodes_validity_predicates: map<BLSPubkey, set<D -> bool>>,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,
        new_honest_nodes_validity_predicates: map<BLSPubkey, set<D -> bool>>
    )
    requires new_honest_nodes_validity_predicates == add_set_of_validity_predicates(existing_honest_nodes_validity_predicates, honest_nodes_validity_predicates)
    ensures new_honest_nodes_validity_predicates.Keys == existing_honest_nodes_validity_predicates.Keys + new_honest_nodes_validity_predicates.Keys
    {

    }

    lemma lemma_add_set_of_validity_predicates2<D(!new, 0)>(
        existing_honest_nodes_validity_predicates: map<BLSPubkey, set<D -> bool>>,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,
        new_honest_nodes_validity_predicates: map<BLSPubkey, set<D -> bool>>,
        n: BLSPubkey,
        vp: D -> bool
    )
    requires new_honest_nodes_validity_predicates == add_set_of_validity_predicates(existing_honest_nodes_validity_predicates, honest_nodes_validity_predicates)
    ensures new_honest_nodes_validity_predicates.Keys == existing_honest_nodes_validity_predicates.Keys + new_honest_nodes_validity_predicates.Keys
    requires n in existing_honest_nodes_validity_predicates.Keys
    requires vp !in existing_honest_nodes_validity_predicates[n]
    requires vp in new_honest_nodes_validity_predicates[n]
    ensures vp == honest_nodes_validity_predicates[n]
    {

    }    

    lemma lemma_add_set_of_validity_predicates3<D(!new, 0)>(
        existing_honest_nodes_validity_predicates: map<BLSPubkey, set<D -> bool>>,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,
        new_honest_nodes_validity_predicates: map<BLSPubkey, set<D -> bool>>,
        n: BLSPubkey,
        vp: D -> bool
    )
    requires new_honest_nodes_validity_predicates == add_set_of_validity_predicates(existing_honest_nodes_validity_predicates, honest_nodes_validity_predicates)
    ensures new_honest_nodes_validity_predicates.Keys == existing_honest_nodes_validity_predicates.Keys + new_honest_nodes_validity_predicates.Keys
    requires n !in existing_honest_nodes_validity_predicates
    requires n in honest_nodes_validity_predicates
    requires vp in new_honest_nodes_validity_predicates[n]
    ensures vp == honest_nodes_validity_predicates[n]
    {

    }      

    function lemma_inv46_b_helper_helper_function(
        s_w_honest_node_states_updated: DVState,
        cid: Slot
    ) : map<BLSPubkey, AttestationData -> bool>
    {
        map n |
                && n in s_w_honest_node_states_updated.honest_nodes_states.Keys 
                && cid in s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.attestation_consensus_active_instances.Keys
            ::
                s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.attestation_consensus_active_instances[cid].validityPredicate
    }    

    // lemma lemma_inv46_b_helper_helper(
    //     s_w_honest_node_states_updated: DVState,
    //     cid: Slot,
    //     validityPredicates: map<BLSPubkey, AttestationData -> bool>,
    //     n: BLSPubkey
    // ) 
    // requires validityPredicates == lemma_inv46_b_helper_helper_function(s_w_honest_node_states_updated, cid)
    // requires n in validityPredicates.Keys
    // // ensures validityPredicates[n] == s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.attestation_consensus_active_instances[cid].validityPredicate
    // {

    // }  

    // // lemma lemma_inv46_b_helper_helper2(
    // //     s_w_honest_node_states_updated: DVState,
    // //     cid: Slot,
    // //     validityPredicates: map<BLSPubkey, AttestationData -> bool>,
    // //     n: BLSPubkey
    // // ) 
    // // requires validityPredicates == lemma_inv46_b_helper_helper_function(s_w_honest_node_states_updated, cid)
    // // requires n in validityPredicates.Keys
    // // requires n !in s_w_honest_node_states_updated.honest_nodes_states
    // // ensures cid in 
    // // // ensures validityPredicates[n] == s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.attestation_consensus_active_instances[cid].validityPredicate
    // // {

    // // } 

    lemma lemma_att_slashing_db_hist_cid_is_monotonic_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        s': DVCNodeState,
        cid: Slot
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state  
    requires cid in process.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures cid in s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures process.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys; 
    {
        var s_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );
        lemma_att_slashing_db_hist_cid_is_monotonic_f_check_for_next_queued_duty(s_mod, s', cid);        
    }           

    lemma lemma_att_slashing_db_hist_cid_is_monotonic_f_att_consensus_decided(
        s: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCNodeState,
        cid: Slot
    )
    requires f_att_consensus_decided.requires(s, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(s, id, decided_attestation_data).state
    requires cid in s.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures cid in s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures s.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys; 
    {
        var local_current_attestation_duty := s.current_attestation_duty.safe_get();
        var attestation_slashing_db := f_update_attestation_slashing_db(s.attestation_slashing_db, decided_attestation_data);

        var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
        var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
        var attestation_signature_share := rs_sign_attestation(decided_attestation_data, fork_version, attestation_signing_root, s.rs);
        var attestation_with_signature_share := AttestationShare(
                aggregation_bits := get_aggregation_bits(local_current_attestation_duty.validator_index),
                data := decided_attestation_data, 
                signature := attestation_signature_share
            ); 

        var s := 
            s.(
                current_attestation_duty := None,
                attestation_shares_to_broadcast := s.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                attestation_slashing_db := attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    s.attestation_consensus_engine_state,
                    attestation_slashing_db
                )
            );

        lemma_att_slashing_db_hist_cid_is_monotonic_f_check_for_next_queued_duty(s, s', cid);             
    }         

    lemma lemma_att_slashing_db_hist_cid_is_monotonic_f_listen_for_new_imported_blocks(
        s: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState,
        cid: Slot
    )
    requires f_listen_for_new_imported_blocks.requires(s, block)
    requires s' == f_listen_for_new_imported_blocks(s, block).state
    requires cid in s.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures cid in s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures s.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys; 
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(s, block);

        var att_consensus_instances_already_decided := s.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(s, att_consensus_instances_already_decided);

        var s :=
                s.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    s.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := s.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := s.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );                     

        if s.current_attestation_duty.isPresent() && s.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            // Stop(current_attestation_duty.safe_get().slot);
            var decided_attestation_data := att_consensus_instances_already_decided[s.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(s.attestation_slashing_db, decided_attestation_data);
            var s := s.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    s.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );
            assert s' == f_check_for_next_queued_duty(s).state;
            lemma_att_slashing_db_hist_cid_is_monotonic_f_check_for_next_queued_duty(s, s', cid);
        }
    }   

    lemma lemma_att_slashing_db_hist_cid_is_monotonic_f_check_for_next_queued_duty(
        s: DVCNodeState,
        s': DVCNodeState,
        cid: Slot
    )
    requires f_check_for_next_queued_duty.requires(s)
    requires s' == f_check_for_next_queued_duty(s).state
    requires cid in s.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures cid in s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures s.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys; 
    decreases s.attestation_duties_queue
    {
        if  && s.attestation_duties_queue != [] 
            && (
                || s.attestation_duties_queue[0].slot in s.future_att_consensus_instances_already_decided
                || !s.current_attestation_duty.isPresent()
            )    
        {
            
            if s.attestation_duties_queue[0].slot in s.future_att_consensus_instances_already_decided.Keys 
            {
                var queue_head := s.attestation_duties_queue[0];
                var new_attestation_slashing_db := f_update_attestation_slashing_db(s.attestation_slashing_db, s.future_att_consensus_instances_already_decided[queue_head.slot]);
                var s_mod := s.(
                    attestation_duties_queue := s.attestation_duties_queue[1..],
                    future_att_consensus_instances_already_decided := s.future_att_consensus_instances_already_decided - {queue_head.slot},
                    attestation_slashing_db := new_attestation_slashing_db,
                    attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                        s.attestation_consensus_engine_state,
                        new_attestation_slashing_db
                    )                        
                );
                lemma_pred_4_1_g_iii_f_check_for_next_queued_duty_updateConsensusInstanceValidityCheck5(
                    s.attestation_consensus_engine_state,
                    new_attestation_slashing_db,
                    s_mod.attestation_consensus_engine_state,
                    cid
                );
                assert s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                lemma_att_slashing_db_hist_cid_is_monotonic_f_check_for_next_queued_duty(s_mod, s', cid);
                assert s.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys; 
            }
            else
            {

            }
        }
    }      

    lemma lemma_att_slashing_db_hist_cid_is_monotonic(
        s: DVCNodeState,
        event: Types.Event,
        s': DVCNodeState,
        outputs: Outputs,
        cid: Slot       
    )
    requires DVCNode_Spec.Next(s, event, s', outputs)
    requires cid in s.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures cid in s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures s.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys;  
    {
        match event
        {
            case ServeAttstationDuty(attestation_duty) => 
                lemma_att_slashing_db_hist_cid_is_monotonic_f_serve_attestation_duty(s, attestation_duty, s', cid);

            case AttConsensusDecided(id, decided_attestation_data) => 
                lemma_att_slashing_db_hist_cid_is_monotonic_f_att_consensus_decided(s, id, decided_attestation_data, s', cid);
            
            case ReceviedAttesttionShare(attestation_share) => 
                assert s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;

            case ImportedNewBlock(block) => 
                lemma_att_slashing_db_hist_cid_is_monotonic_f_listen_for_new_imported_blocks(s, block, s', cid);
            
            case ResendAttestationShares => 
                assert s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
        
            case NoEvent => 
                assert s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;

        }           
    } 

    lemma lemma_att_slashing_db_hist_cid_is_monotonic_corollary(
        s: DVCNodeState,
        event: Types.Event,
        s': DVCNodeState,
        outputs: Outputs,
        cid: Slot,
        vp: AttestationData -> bool       
    )
    requires DVCNode_Spec.Next(s, event, s', outputs)
    requires cid in s.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    requires vp in s.attestation_consensus_engine_state.att_slashing_db_hist[cid]
    ensures cid in s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures vp in s'.attestation_consensus_engine_state.att_slashing_db_hist[cid]
    {
        lemma_att_slashing_db_hist_cid_is_monotonic(s, event, s', outputs, cid);
    }          

    lemma lemma_inv46_b_helper(
        s: DVState,
        event: DV.Event,
        cid: Slot,
        vp: AttestationData -> bool,
        hn: BLSPubkey,
        s': DVState
    )
    requires NextEvent(s, event, s')
    requires inv1(s)
    requires inv53(s)
    requires inv3(s)    
    requires hn in s.honest_nodes_states.Keys
    requires inv33_body(s, hn, s.honest_nodes_states[hn], cid)
    requires inv46_b_body(s, hn, s.honest_nodes_states[hn], cid, vp)
    requires inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(s)
    requires inv_attestation_consensus_active_instances_predicate_is_in_att_slashing_db_hist_body(s.honest_nodes_states[hn], cid)
    ensures inv46_b_body(s', hn, s'.honest_nodes_states[hn], cid, vp)
    {
        // lemma_inv_33_helper(s, event, cid, hn, s');
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>

                var s_w_honest_node_states_updated := lemma_pred_4_1_f_g_i_get_s_w_honest_node_states_updated(s, node, nodeEvent);           

                assert s_w_honest_node_states_updated.consensus_on_attestation_data == s.consensus_on_attestation_data;


                var output := 
                    if nodeEvent.AttConsensusDecided? && nodeEvent.id == cid then 
                        Some(Decided(node, nodeEvent.decided_attestation_data))
                    else
                        None
                    ;

                var validityPredicates := lemma_inv46_b_helper_helper_function(s_w_honest_node_states_updated, cid);
                    // map n |
                    //         && n in s_w_honest_node_states_updated.honest_nodes_states.Keys 
                    //         && cid in s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.attestation_consensus_active_instances.Keys
                    //     ::
                    //         s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.attestation_consensus_active_instances[cid].validityPredicate
                    // ;

                var s_consensus := s_w_honest_node_states_updated.consensus_on_attestation_data[cid];
                var s'_consensus := s'.consensus_on_attestation_data[cid];                

                assert
                    ConsensusSpec.Next(
                        s_consensus,
                        validityPredicates,
                        s'_consensus,
                        output
                    );
                
                var hn_state := s.honest_nodes_states[hn];
                var hn'_state := s'.honest_nodes_states[hn];

                if 
                    && hn in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions.Keys
                    && vp in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions[hn]                          
                    && cid in hn'_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
          
                   
                {
                    // assert s'_consensus.honest_nodes_validity_functions == add_set_of_validity_predicates(s_consensus.honest_nodes_validity_functions, validityPredicates);
                    if hn in  s.consensus_on_attestation_data[cid].honest_nodes_validity_functions.Keys
                    {
                        if vp in s.consensus_on_attestation_data[cid].honest_nodes_validity_functions[hn]
                        {
                            assert cid in hn'_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                            assert vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[cid];
                        }
                        else 
                        {
                            lemma_add_set_of_validity_predicates2(
                                s_consensus.honest_nodes_validity_functions, 
                                validityPredicates,
                                s'_consensus.honest_nodes_validity_functions,
                                hn,
                                vp
                            );
                            assert vp == s.honest_nodes_states[hn].attestation_consensus_engine_state.attestation_consensus_active_instances[cid].validityPredicate; 
                            assert vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[cid];
                        }
                    }
                    else 
                    {
                        assert hn in validityPredicates;
                        assert hn !in  s_consensus.honest_nodes_validity_functions.Keys;
                        // assert cid in s.honest_nodes_states[hn].attestation_consensus_engine_state.attestation_consensus_active_instances.Keys;
                        // assert vp == s.honest_nodes_states[hn].attestation_consensus_engine_state.attestation_consensus_active_instances[cid].validityPredicate; 
                        
                        lemma_add_set_of_validity_predicates3(
                            s_consensus.honest_nodes_validity_functions, 
                            validityPredicates,
                            s'_consensus.honest_nodes_validity_functions,
                            hn,
                            vp
                        );

                        assert vp == s.honest_nodes_states[hn].attestation_consensus_engine_state.attestation_consensus_active_instances[cid].validityPredicate; 
                        assert vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[cid];

                    }
                    assert vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[cid];

                    if hn == node 
                    {
                        assert DVCNode_Spec.Next(s_w_honest_node_states_updated.honest_nodes_states[hn], nodeEvent, s'.honest_nodes_states[hn], nodeOutputs);
                        lemma_att_slashing_db_hist_cid_is_monotonic_corollary(s_w_honest_node_states_updated.honest_nodes_states[hn], nodeEvent, s'.honest_nodes_states[hn], nodeOutputs, cid, vp);
                        // assert s_w_honest_node_states_updated.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                        // assert cid in s'.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                        assert vp in hn'_state.attestation_consensus_engine_state.att_slashing_db_hist[cid];
                    }
                    else 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        assert vp in hn'_state.attestation_consensus_engine_state.att_slashing_db_hist[cid];
                    }   
                    assert vp in hn'_state.attestation_consensus_engine_state.att_slashing_db_hist[cid];                 

                }  

                         
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) => 
                assert s'.consensus_on_attestation_data == s.consensus_on_attestation_data;
                assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                 
                if
                    && hn in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions.Keys
                    && vp in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions[hn]                          
                    && cid in s'.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys
                {
                    assert inv33_body(s, hn, s.honest_nodes_states[hn], cid);
                    assert cid in s.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                    assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                    assert cid in s'.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                    assert vp in s'.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist[cid];                 
                    
                } 

        }
    }  

    lemma lemma_inv46_b(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEvent(s, event, s')
    requires inv1(s)
    requires inv53(s)
    requires inv3(s)    
    requires inv33(s)  
    requires inv46_b(s) 
    requires inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(s)
    requires inv_attestation_consensus_active_instances_predicate_is_in_att_slashing_db_hist(s)
    ensures inv46_b(s')   
    {
        forall hn: BLSPubkey, slot: Slot, vp : AttestationData -> bool |
            hn in s'.honest_nodes_states
        ensures inv46_b_body(s', hn, s'.honest_nodes_states[hn], slot, vp)    
        {
            lemma_inv46_b_helper(s, event, slot, vp, hn, s');
        }
    }  

    lemma lemmaStartConsensusInstance(
        s: ConsensusEngineState,
        id: Slot,
        attestation_duty: AttestationDuty,
        attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState        
    ) 
    requires id !in s.attestation_consensus_active_instances.Keys 
    requires s' ==   startConsensusInstance(s, id, attestation_duty, attestation_slashing_db)
    ensures s'.att_slashing_db_hist.Keys == s.att_slashing_db_hist.Keys + {id}
    {    
    }

    lemma lemmaStartConsensusInstance4(
        s: ConsensusEngineState,
        id: Slot,
        attestation_duty: AttestationDuty,
        attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState,
        vp: AttestationData -> bool
    ) 
    requires id !in s.attestation_consensus_active_instances.Keys 
    requires id in s.att_slashing_db_hist.Keys
    requires vp in s.att_slashing_db_hist[id].Keys
    requires s' ==   startConsensusInstance(s, id, attestation_duty, attestation_slashing_db)
    ensures id in s'.att_slashing_db_hist.Keys
    ensures vp in s'.att_slashing_db_hist[id]
    ensures s.att_slashing_db_hist[id][vp] <= s'.att_slashing_db_hist[id][vp]
    {    
    }       

    lemma lemmaStartConsensusInstance5(
        s: ConsensusEngineState,
        id: Slot,
        attestation_duty: AttestationDuty,
        attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState
    ) 
    requires id !in s.attestation_consensus_active_instances.Keys 
    requires id in s.att_slashing_db_hist.Keys
    requires s' ==   startConsensusInstance(s, id, attestation_duty, attestation_slashing_db)
    ensures id in s'.att_slashing_db_hist.Keys
    ensures s.att_slashing_db_hist[id].Keys <= s'.att_slashing_db_hist[id].Keys
    // ensures s'.att_slashing_db_hist[id] == {}
    {    
    } 

    lemma lemma_pred_4_1_g_iii_a_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state  
    requires index_next_attestation_duty_to_be_served > 0    
    requires inv_g_iii_a_body_body(dvn, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served-1)
    requires lemma_ServeAttstationDuty2_predicate(dvn, index_next_attestation_duty_to_be_served, attestation_duty, n)
    ensures inv_g_iii_a_body_body(dvn, n, s', index_next_attestation_duty_to_be_served)
    {
        var new_p := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
        );

        lemma_pred_4_1_g_iii_a_f_check_for_next_queued_duty(new_p, s', dvn, n, index_next_attestation_duty_to_be_served);
    }       

    lemma lemma_pred_4_1_g_iii_a_f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(process, id, decided_attestation_data).state
    requires inv_g_iii_a_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)    
    ensures inv_g_iii_a_body_body(dvn, n, s', index_next_attestation_duty_to_be_served)
      
    {
        // TODO: Remove below by changing spec
        assume id == process.current_attestation_duty.safe_get().slot;        
        var local_current_attestation_duty := process.current_attestation_duty.safe_get();
        var attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);

        var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
        var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
        var attestation_signature_share := rs_sign_attestation(decided_attestation_data, fork_version, attestation_signing_root, process.rs);
        var attestation_with_signature_share := AttestationShare(
                aggregation_bits := get_aggregation_bits(local_current_attestation_duty.validator_index),
                data := decided_attestation_data, 
                signature := attestation_signature_share
            ); 

        var s_mod := 
            process.(
                current_attestation_duty := None,
                attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                attestation_slashing_db := attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    process.attestation_consensus_engine_state,
                    attestation_slashing_db
                )
            );



        lemma_pred_4_1_g_iii_a_f_check_for_next_queued_duty(s_mod, s', dvn, n, index_next_attestation_duty_to_be_served);             
    }    

    lemma lemma_pred_4_1_g_iii_a_f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_g_iii_a_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)    
    ensures inv_g_iii_a_body_body(dvn, n, s', index_next_attestation_duty_to_be_served)
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var new_process :=
                process.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );                     

        if new_process.current_attestation_duty.isPresent() && new_process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            // Stop(current_attestation_duty.safe_get().slot);
            var decided_attestation_data := att_consensus_instances_already_decided[new_process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(new_process.attestation_slashing_db, decided_attestation_data);
            var s_mod := new_process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    new_process.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );
                   
            lemma_pred_4_1_g_iii_a_f_check_for_next_queued_duty(s_mod, s', dvn, n, index_next_attestation_duty_to_be_served);                    
        }        
    }        


    lemma lemma_pred_4_1_g_iii_a_f_check_for_next_queued_duty(
        process: DVCNodeState,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state  
    requires inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)
    requires inv_g_iii_a_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    ensures inv_g_iii_a_body_body(dvn, n, s', index_next_attestation_duty_to_be_served)
    decreases process.attestation_duties_queue
    {
        if  && process.attestation_duties_queue != [] 
            && (
                || process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided
                || !process.current_attestation_duty.isPresent()
            )    
        {
            if process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided.Keys
            {
                var queue_head := process.attestation_duties_queue[0];
                var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, process.future_att_consensus_instances_already_decided[queue_head.slot]);
                var s_mod := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..],
                    future_att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided - {queue_head.slot},
                    attestation_slashing_db := new_attestation_slashing_db,
                    attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                        process.attestation_consensus_engine_state,
                        new_attestation_slashing_db
                    )                        
                );

                lemma_pred_4_1_g_iii_f_check_for_next_queued_duty_updateConsensusInstanceValidityCheck(
                    process.attestation_consensus_engine_state,
                    new_attestation_slashing_db,
                    s_mod.attestation_consensus_engine_state
                );

                assert s_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys == process.attestation_consensus_engine_state.att_slashing_db_hist.Keys;

                forall ad  |
                    && ad in s_mod.attestation_duties_queue
                ensures ad in process.attestation_duties_queue
                {
                    var i :| 0 <= i < |s_mod.attestation_duties_queue|
                                && s_mod.attestation_duties_queue[i] == ad;
                    assert ad in process.attestation_duties_queue;
                }                 

                lemma_pred_4_1_g_iii_a_f_check_for_next_queued_duty(s_mod, s', dvn, n, index_next_attestation_duty_to_be_served);
            }
            else 
            {        
                lemmaStartConsensusInstance(
                    process.attestation_consensus_engine_state,
                    process.attestation_duties_queue[0].slot,
                    process.attestation_duties_queue[0],
                    process.attestation_slashing_db,
                    s'.attestation_consensus_engine_state
                );

                forall slot  |
                    slot in s'.attestation_consensus_engine_state.att_slashing_db_hist
                ensures 
                            exists i: nat :: 
                                && i < index_next_attestation_duty_to_be_served
                                && var an := dvn.sequence_attestation_duties_to_be_served[i];
                                && an.attestation_duty.slot == slot 
                                && an.node == n
                        ;                                    
                {
                    if slot in process.attestation_consensus_engine_state.att_slashing_db_hist
                    {
                        assert 
                            exists i: nat :: 
                                && i < index_next_attestation_duty_to_be_served
                                && var an := dvn.sequence_attestation_duties_to_be_served[i];
                                && an.attestation_duty.slot == slot 
                                && an.node == n
                        ;
                    }
                    else
                    {
                        assert slot == process.attestation_duties_queue[0].slot;
                        // assert slot in process.attestation_duties_queue.Keys;
                        assert process.attestation_duties_queue[0] in process.attestation_duties_queue;
                        assert 
                            exists i: nat :: 
                                && i < index_next_attestation_duty_to_be_served
                                && var an := dvn.sequence_attestation_duties_to_be_served[i];
                                && an.attestation_duty.slot == slot 
                                && an.node == n
                        ;                        
                    }
                }
                
            }
        } 
        else 
        {
        }             
    }

    lemma lemma_pred_4_1_g_iii_a_helper_honest_helper4(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCNodeState,
        n: BLSPubkey
    )
    requires NextEvent(s, event, s')    
    requires inv_g_iii_a_body_body(s, n, s_node, s.index_next_attestation_duty_to_be_served)
    requires inv_g_iii_b_body_body(s, n, s_node, s.index_next_attestation_duty_to_be_served)
    // requires inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist_body_body(s_node)


    ensures inv_g_iii_a_body_body(s', n, s_node, s.index_next_attestation_duty_to_be_served)
    ensures inv_g_iii_b_body_body(s', n, s_node, s.index_next_attestation_duty_to_be_served)
    {


        
    }       

    lemma lemma_pred_4_1_g_iii_a_helper_honest(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires pred_4_1_g_iii_a(s)
    requires inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(s)
    requires pred_4_1_g_iii_b(s)    
    requires NextEvent(s, event, s')
    requires event.HonestNodeTakingStep?
    ensures inv_g_iii_a_body_body(s', event.node, s'.honest_nodes_states[event.node], s'.index_next_attestation_duty_to_be_served); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lemma_pred_4_1_g_iii_a_helper_honest_helper4(s, event, s', s_node, node);

                assert inv_g_iii_a_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_g_iii_b_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);      
                assert inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist_body_body(s_node);     

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lemma_ServeAttstationDuty2(s, event, s');
                        lemma_pred_4_1_g_iii_a_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_g_iii_a_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        lemma_NonServeAttstationDuty(s, event, s');
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lemma_pred_4_1_g_iii_a_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_g_iii_a_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                        
               
                   
                    case ReceviedAttesttionShare(attestation_share) =>
                        lemma_NonServeAttstationDuty(s, event, s'); 
                        lemma_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        // lemma_pred_4_1_g_iii_a_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_iii_a_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  
                        

                    case ImportedNewBlock(block) => 
                        lemma_NonServeAttstationDuty(s, event, s');
                        var s_node2 := add_block_to_bn(s_node, nodeEvent.block);
                        lemma_pred_4_1_g_iii_a_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_g_iii_a_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                     
                    
                 
                    case ResendAttestationShares => 
                        lemma_NonServeAttstationDuty(s, event, s');
                        lemma_f_resend_attestation_share_constants(s_node, s'_node);
                        // lemma_pred_4_1_g_iii_a_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_iii_a_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  

                    case NoEvent => 
                        lemma_NonServeAttstationDuty(s, event, s');
                        assert s_node == s'_node; 
                        // lemma_pred_4_1_g_iii_a_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_iii_a_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                          
                }                     

        }
    }   

    lemma lemma_pred_4_1_g_iii_a(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEvent(s, event, s')
    requires pred_4_1_g_iii_a(s)
    requires inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(s)
    requires pred_4_1_g_iii_b(s) 
    ensures pred_4_1_g_iii_a(s');  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lemma_pred_4_1_g_iii_a_helper_honest(s, event, s');
                   
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_g_iii_a_body_body(s', hn, s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lemma_pred_4_1_g_iii_a_helper_honest_helper4(s, event, s', s.honest_nodes_states[hn], hn);
                    }
                }  
                assert pred_4_1_g_iii_a(s');
                         
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_g_iii_a_body_body(s', hn, s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served); 
                {
                    // if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lemma_pred_4_1_g_iii_a_helper_honest_helper4(s, event, s', s.honest_nodes_states[hn], hn);
                    }
                }  
                assert pred_4_1_g_iii_a(s');            


        }
    }  

    lemma lemma_pred_4_1_g_iii_a_a_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state  
    requires index_next_attestation_duty_to_be_served > 0    
    requires inv_g_iii_a_a_body_body(dvn, n, process)
    requires inv_head_attetation_duty_queue_higher_than_latest_attestation_duty_body_body(process)
    requires inv_attestation_duty_queue_is_ordered_body_body(process) 
    requires inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)   
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_g_iii_c_body_body(dvn, n, process, index_next_attestation_duty_to_be_served-1)
    requires is_sequence_attestation_duties_to_be_served_orderd(dvn);
    requires lemma_ServeAttstationDuty2_predicate(dvn, index_next_attestation_duty_to_be_served, attestation_duty, n)
    ensures inv_g_iii_a_a_body_body(dvn, n, s')
    {
        var new_p := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
        );

        if process.attestation_duties_queue != []
        {
            assert inv_attestation_duty_queue_is_ordered_body_body(new_p); 
        }
        else 
        {
            assert inv_attestation_duty_queue_is_ordered_body_body(new_p); 
        }        

        lemma_pred_4_1_g_iii_a_a_f_check_for_next_queued_duty(new_p, s', dvn, n);
    }  

    lemma lemma_pred_4_1_g_iii_a_a_f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(process, id, decided_attestation_data).state
    requires inv_g_iii_a_a_body_body(dvn, n, process)
    requires inv_head_attetation_duty_queue_higher_than_latest_attestation_duty_body_body(process)
    requires inv_attestation_duty_queue_is_ordered_body_body(process) 
    requires inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)   
    ensures inv_g_iii_a_a_body_body(dvn, n, s') 
    {
        // TODO: Remove below by changing spec
        assume id == process.current_attestation_duty.safe_get().slot;        
        var local_current_attestation_duty := process.current_attestation_duty.safe_get();
        var attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);

        var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
        var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
        var attestation_signature_share := rs_sign_attestation(decided_attestation_data, fork_version, attestation_signing_root, process.rs);
        var attestation_with_signature_share := AttestationShare(
                aggregation_bits := get_aggregation_bits(local_current_attestation_duty.validator_index),
                data := decided_attestation_data, 
                signature := attestation_signature_share
            ); 

        var s_mod := 
            process.(
                current_attestation_duty := None,
                attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                attestation_slashing_db := attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    process.attestation_consensus_engine_state,
                    attestation_slashing_db
                )
            );



        lemma_pred_4_1_g_iii_a_a_f_check_for_next_queued_duty(s_mod, s', dvn, n);             
    }        

    lemma lemma_pred_4_1_g_iii_a_a_f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_g_iii_a_a_body_body(dvn, n, process)
    requires inv_head_attetation_duty_queue_higher_than_latest_attestation_duty_body_body(process)
    requires inv_attestation_duty_queue_is_ordered_body_body(process) 
    requires inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)   
    ensures inv_g_iii_a_a_body_body(dvn, n, s')
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var new_process :=
                process.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );                     

        if new_process.current_attestation_duty.isPresent() && new_process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            // Stop(current_attestation_duty.safe_get().slot);
            var decided_attestation_data := att_consensus_instances_already_decided[new_process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(new_process.attestation_slashing_db, decided_attestation_data);
            var s_mod := new_process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    new_process.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );
                   
            lemma_pred_4_1_g_iii_a_a_f_check_for_next_queued_duty(s_mod, s', dvn, n);                    
        }        
    }            

    lemma lemma_pred_4_1_g_iii_a_a_f_check_for_next_queued_duty(
        process: DVCNodeState,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state  
    requires inv_g_iii_a_a_body_body(dvn, n, process)
    requires inv_head_attetation_duty_queue_higher_than_latest_attestation_duty_body_body(process)
    requires inv_attestation_duty_queue_is_ordered_body_body(process) 
    requires inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)   
    ensures inv_g_iii_a_a_body_body(dvn, n, s')
    decreases process.attestation_duties_queue
    {
        if  && process.attestation_duties_queue != [] 
            && (
                || process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided
                || !process.current_attestation_duty.isPresent()
            )    
        {
            if process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided.Keys
            {
                var queue_head := process.attestation_duties_queue[0];
                var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, process.future_att_consensus_instances_already_decided[queue_head.slot]);
                var s_mod := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..],
                    future_att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided - {queue_head.slot},
                    attestation_slashing_db := new_attestation_slashing_db,
                    attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                        process.attestation_consensus_engine_state,
                        new_attestation_slashing_db
                    )                        
                );
           
                lemma_pred_4_1_g_iii_a_a_f_check_for_next_queued_duty(
                    s_mod,
                    s',
                    dvn,
                    n
                );

            }
            else 
            {       
                assert inv_g_iii_a_a_body_body(dvn, n, s'); 
            }
        } 
        else 
        {
        }             
    }  

    lemma lemma_pred_4_1_g_iii_a_a_helper_honest_helper1(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCNodeState,
        n: BLSPubkey
    )
    requires NextEvent(s, event, s')    
    requires inv_g_iii_a_a_body_body(s, n, s_node)
    ensures inv_g_iii_a_a_body_body(s', n, s_node)
    {

    }

    lemma lemma_pred_4_1_g_iii_a_a_helper_honest_helper2(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCNodeState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires NextEvent(s, event, s')    
    requires inv_g_iii_b_body_body(s, n, s_node, index_next_attestation_duty_to_be_served)
    requires inv_g_iii_c_body_body(s, n, s_node, index_next_attestation_duty_to_be_served)
    requires is_sequence_attestation_duties_to_be_served_orderd(s);

    ensures inv_g_iii_b_body_body(s', n, s_node, index_next_attestation_duty_to_be_served)
    ensures inv_g_iii_c_body_body(s', n, s_node, index_next_attestation_duty_to_be_served)
    ensures is_sequence_attestation_duties_to_be_served_orderd(s')
    {
        
    }    

    lemma lemma_pred_4_1_g_iii_a_a_helper_honest(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires pred_4_1_g_iii_a_a(s)
    requires inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(s)
    requires inv_attestation_duty_queue_is_ordered(s) 
    requires inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(s)   
    requires pred_4_1_g_iii_b(s)
    requires pred_4_1_g_iii_c(s)
    requires is_sequence_attestation_duties_to_be_served_orderd(s);    
    requires NextEvent(s, event, s')
    requires event.HonestNodeTakingStep?
    ensures inv_g_iii_a_a_body_body(s', event.node, s'.honest_nodes_states[event.node]); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lemma_pred_4_1_g_iii_a_a_helper_honest_helper1(s, event, s', s_node, node);
                lemma_pred_4_1_g_iii_a_a_helper_honest_helper2(s, event, s', s_node, node, s.index_next_attestation_duty_to_be_served);

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lemma_ServeAttstationDuty2(s, event, s');
                        lemma_pred_4_1_g_iii_a_a_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_g_iii_a_a_body_body(s', node, s'_node);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        lemma_NonServeAttstationDuty(s, event, s');
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lemma_pred_4_1_g_iii_a_a_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_g_iii_a_a_body_body(s', node, s'_node);                        
               
                   
                    case ReceviedAttesttionShare(attestation_share) =>
                        lemma_NonServeAttstationDuty(s, event, s'); 
                        lemma_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        assert inv_g_iii_a_a_body_body(s', node, s'_node);  
                        

                    case ImportedNewBlock(block) => 
                        lemma_NonServeAttstationDuty(s, event, s');
                        var s_node2 := add_block_to_bn(s_node, nodeEvent.block);
                        lemma_pred_4_1_g_iii_a_a_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_g_iii_a_a_body_body(s', node, s'_node);                     
                    
                 
                    case ResendAttestationShares => 
                        lemma_NonServeAttstationDuty(s, event, s');
                        lemma_f_resend_attestation_share_constants(s_node, s'_node);
                        // lemma_pred_4_1_g_iii_a_a_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_iii_a_a_body_body(s', node, s'_node);  

                    case NoEvent => 
                        lemma_NonServeAttstationDuty(s, event, s');
                        assert s_node == s'_node; 
                        assert inv_g_iii_a_a_body_body(s', node, s'_node);                          
                }                     

        }
    }           

    lemma lemma_pred_4_1_g_iii_a_a(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEvent(s, event, s')
    requires pred_4_1_g_iii_a_a(s)
    requires inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(s)
    requires inv_attestation_duty_queue_is_ordered(s) 
    requires inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(s)   
    requires pred_4_1_g_iii_b(s)
    requires pred_4_1_g_iii_c(s)
    requires is_sequence_attestation_duties_to_be_served_orderd(s);
    ensures pred_4_1_g_iii_a_a(s');  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lemma_pred_4_1_g_iii_a_a_helper_honest(s, event, s');
                   
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_g_iii_a_a_body_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lemma_pred_4_1_g_iii_a_a_helper_honest_helper1(s, event, s', s.honest_nodes_states[hn], hn);
                    }
                }  
                assert pred_4_1_g_iii_a_a(s');
                         
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lemma_pred_4_1_g_iii_a_a_helper_honest(s, event, s');
                   
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_g_iii_a_a_body_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    // if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lemma_pred_4_1_g_iii_a_a_helper_honest_helper1(s, event, s', s.honest_nodes_states[hn], hn);
                    }
                }  
                assert pred_4_1_g_iii_a_a(s');            
         


        }
    }        

}