include "../../../../common/commons.dfy"
include "../../common/attestation_creation_instrumented.dfy"
include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_attestation_creation.dfy"
include "../../../../specs/dvc/dvc_attestation_creation.dfy"

include "../../../common/helper_sets_lemmas.dfy"
include "../../../no_slashable_attestations/common/common_proofs.dfy"
include "../../../no_slashable_attestations/common/dvc_spec_axioms.dfy"

include "invs_dv_next_1.dfy"
include "invs_dv_next_2.dfy"
include "invs_dv_next_3.dfy"
include "invs_dv_next_4.dfy"

include "../inv.dfy"

include "../../../common/helper_pred_fcn.dfy"


module Invs_DV_Next_5
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Spec
    import opened DV    
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Helper_Sets_Lemmas
    import opened Invs_DV_Next_1
    import opened Invs_DV_Next_2
    import opened Invs_DV_Next_3
    import opened Invs_DV_Next_4
    import opened Common_Proofs
    import opened DVC_Spec_Axioms
    import opened Helper_Pred_Fcn

    lemma lem_att_slashing_db_hist_is_monotonic_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state  
    ensures process.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
    {
        var s_mod := f_enqueue_new_att_duty(
                            process,
                            attestation_duty
                        );
        lem_att_slashing_db_hist_is_monotonic_f_check_for_next_duty(s_mod, s');        
    }       

    lemma lem_att_slashing_db_hist_is_monotonic_f_att_consensus_decided(
        s: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCState
    )
    requires f_att_consensus_decided.requires(s, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(s, id, decided_attestation_data).state
    ensures s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;   
    {
        if  || !s.current_attestation_duty.isPresent()
            || id != s.current_attestation_duty.safe_get().slot 
        {
            return;
        }

        var s_mod := f_update_process_after_att_duty_decided(
                                s,
                                id,
                                decided_attestation_data);

        lem_att_slashing_db_hist_is_monotonic_f_check_for_next_duty(s_mod, s');             
    }     

    lemma lem_att_slashing_db_hist_is_monotonic_f_listen_for_new_imported_blocks(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(s, block)
    requires s' == f_listen_for_new_imported_blocks(s, block).state
    ensures s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys; 
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(s, block);

        var att_consensus_instances_already_decided := s.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(s, att_consensus_instances_already_decided);

        var s := f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                s,
                                block
                            );                  

        if pred_listen_for_new_imported_blocks_checker(s, att_consensus_instances_already_decided)
        {
            var s := f_updateConsensusInstanceValidityCheck_in_listen_for_new_imported_blocks(
                                    s,
                                    att_consensus_instances_already_decided
                                );
            assert s' == f_check_for_next_duty(s).state;
            lem_att_slashing_db_hist_is_monotonic_f_check_for_next_duty(s, s');
        }
    }      

    lemma lem_att_slashing_db_hist_is_monotonic_f_check_for_next_duty(
        s: DVCState,
        s': DVCState
    )
    requires f_check_for_next_duty.requires(s)
    requires s' == f_check_for_next_duty(s).state
    ensures s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
    decreases s.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(s)      
        {            
            if first_queued_att_duty_was_decided(s)
            {
                var s_mod := f_dequeue_attestation_duties_queue(s);

                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_duty_updateConsensusInstanceValidityCheck(
                    s.attestation_consensus_engine_state,
                    s_mod.attestation_slashing_db,
                    s_mod.attestation_consensus_engine_state
                );
                assert s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                lem_att_slashing_db_hist_is_monotonic_f_check_for_next_duty(s_mod, s');
            }
            else
            {
            }
        }
    }      

    lemma lem_att_slashing_db_hist_is_monotonic(
        s: DVCState,
        event: Types.Event,
        s': DVCState,
        outputs: Outputs        
    )
    requires DVC_Spec.Next.requires(s, event, s', outputs)
    requires DVC_Spec.Next(s, event, s', outputs)
    ensures s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
    {
        match event
        {
            case ServeAttstationDuty(attestation_duty) => 
                lem_att_slashing_db_hist_is_monotonic_f_serve_attestation_duty(s, attestation_duty, s');

            case AttConsensusDecided(id, decided_attestation_data) => 
                lem_att_slashing_db_hist_is_monotonic_f_att_consensus_decided(s, id, decided_attestation_data, s');
            
            case ReceivedAttestationShare(attestation_share) => 
                assert s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;

            case ImportedNewBlock(block) => 
                lem_att_slashing_db_hist_is_monotonic_f_listen_for_new_imported_blocks(s, block, s');
            
            case ResendAttestationShares => 
                assert s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
        
            case NoEvent => 
                assert s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;

        }        
    }

    lemma lem_NextEvent_implies_NextHonestAfterAddingBlockToBn_and_DVC_Spec_Next(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    ensures NextHonestAfterAddingBlockToBn.requires(add_block_to_bn_with_event(s, event.node, event.event), event.node, event.event, event.nodeOutputs, s' )  
    ensures NextHonestAfterAddingBlockToBn(add_block_to_bn_with_event(s, event.node, event.event), event.node, event.event, event.nodeOutputs, s' )  
    ensures DVC_Spec.Next.requires(add_block_to_bn_with_event(s, event.node, event.event).honest_nodes_states[event.node], event.event, s'.honest_nodes_states[event.node], event.nodeOutputs);    
    ensures DVC_Spec.Next(add_block_to_bn_with_event(s, event.node, event.event).honest_nodes_states[event.node], event.event, s'.honest_nodes_states[event.node], event.nodeOutputs);
    {

    } 

    lemma lem_inv_33_helper(
        s: DVState,
        event: DV.Event,
        cid: Slot,
        hn: BLSPubkey,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_quorum_constraints(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)    
    requires hn in s.honest_nodes_states.Keys
    requires inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper_body(s, hn, s.honest_nodes_states[hn], cid)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(s)
    ensures inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper_body(s', hn, s'.honest_nodes_states[hn], cid)
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>

                var s_w_honest_node_states_updated := lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_get_s_w_honest_node_states_updated(s, node, nodeEvent);           

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
                            && cid in s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
                        ::
                            s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances[cid].validityPredicate
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
                        assert inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper_body(s, hn, s.honest_nodes_states[hn], cid);

                        assert cid in s.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                    }
                    else 
                    {
                        assert hn in validityPredicates;
                        assert cid in s.honest_nodes_states[hn].attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;
                        assert inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(s.honest_nodes_states[hn]);
                        assert cid in s.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                    }

                    if hn == node 
                    {
                        lem_NextEvent_implies_NextHonestAfterAddingBlockToBn_and_DVC_Spec_Next(s, event, s');
                        assert DVC_Spec.Next.requires(s_w_honest_node_states_updated.honest_nodes_states[hn], nodeEvent, s'.honest_nodes_states[hn], nodeOutputs);
                        assert DVC_Spec.Next(s_w_honest_node_states_updated.honest_nodes_states[hn], nodeEvent, s'.honest_nodes_states[hn], nodeOutputs);
                        lem_att_slashing_db_hist_is_monotonic(s_w_honest_node_states_updated.honest_nodes_states[hn], nodeEvent, s'.honest_nodes_states[hn], nodeOutputs);
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
                    assert inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper_body(s, hn, s.honest_nodes_states[hn], cid);
                    assert cid in s.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                    assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                    assert cid in s'.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys;                    
                } 

        }
    }   

    lemma lem_inv_33(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_quorum_constraints(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)    
    requires inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper(s)   
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(s)
    ensures inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper(s')   
    {
        forall hn: BLSPubkey, slot: Slot |
            hn in s'.honest_nodes_states
        ensures inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper_body(s', hn, s'.honest_nodes_states[hn], slot)    
        {
            lem_inv_33_helper(s, event, slot, hn, s');
        }
    }  

    lemma lem_inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper_implies_46_a(dv: DVState)
    requires inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper(dv)
    ensures inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv)
    {
        forall hn: BLSPubkey, s: Slot | is_honest_node(dv, hn)
        ensures
                var hn_state := dv.honest_nodes_states[hn];
                && ( hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
                    ==> s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys)
                ;        
        {
            assert hn in dv.honest_nodes_states.Keys;
            var hn_state := dv.honest_nodes_states[hn];
            assert inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper_body(dv, hn, hn_state, s);
            assert
                && ( hn in dv.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
                    ==> s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys)
                ;
        }
    }  

    lemma lem_inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_quorum_constraints(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)   
    requires inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper(s)   
    requires inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(s)   
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(s)
    ensures inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(s')   
    {
        lem_inv_33(s, event, s');
        lem_inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper_implies_46_a(s');
    }     

    lemma lem_add_set_of_validity_predicates<D(!new, 0)>(
        existing_honest_nodes_validity_predicates: map<BLSPubkey, set<D -> bool>>,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,
        new_honest_nodes_validity_predicates: map<BLSPubkey, set<D -> bool>>
    )
    requires new_honest_nodes_validity_predicates == add_set_of_validity_predicates(existing_honest_nodes_validity_predicates, honest_nodes_validity_predicates)
    ensures new_honest_nodes_validity_predicates.Keys == existing_honest_nodes_validity_predicates.Keys + new_honest_nodes_validity_predicates.Keys
    {

    }

    lemma lem_add_set_of_validity_predicates2<D(!new, 0)>(
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

    lemma lem_add_set_of_validity_predicates3<D(!new, 0)>(
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

    function lem_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_helper_helper_function(
        s_w_honest_node_states_updated: DVState,
        cid: Slot
    ) : map<BLSPubkey, AttestationData -> bool>
    {
        map n |
                && n in s_w_honest_node_states_updated.honest_nodes_states.Keys 
                && cid in s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
            ::
                s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances[cid].validityPredicate
    }    

    // lemma lem_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_helper_helper(
    //     s_w_honest_node_states_updated: DVState,
    //     cid: Slot,
    //     validityPredicates: map<BLSPubkey, AttestationData -> bool>,
    //     n: BLSPubkey
    // ) 
    // requires validityPredicates == lem_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_helper_helper_function(s_w_honest_node_states_updated, cid)
    // requires n in validityPredicates.Keys
    // // ensures validityPredicates[n] == s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances[cid].validityPredicate
    // {

    // }  

    // // lemma lem_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_helper_helper2(
    // //     s_w_honest_node_states_updated: DVState,
    // //     cid: Slot,
    // //     validityPredicates: map<BLSPubkey, AttestationData -> bool>,
    // //     n: BLSPubkey
    // // ) 
    // // requires validityPredicates == lem_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_helper_helper_function(s_w_honest_node_states_updated, cid)
    // // requires n in validityPredicates.Keys
    // // requires n !in s_w_honest_node_states_updated.honest_nodes_states
    // // ensures cid in 
    // // // ensures validityPredicates[n] == s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances[cid].validityPredicate
    // // {

    // // } 

    lemma lem_att_slashing_db_hist_cid_is_monotonic_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState,
        cid: Slot
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state  
    requires cid in process.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures cid in s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures process.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys; 
    {
        var s_mod := f_enqueue_new_att_duty(
                            process,
                            attestation_duty
                        );
        lem_att_slashing_db_hist_cid_is_monotonic_f_check_for_next_duty(s_mod, s', cid);        
    }           

    lemma lem_att_slashing_db_hist_cid_is_monotonic_f_att_consensus_decided(
        s: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCState,
        cid: Slot
    )
    requires f_att_consensus_decided.requires(s, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(s, id, decided_attestation_data).state
    requires cid in s.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures cid in s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures s.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys; 
    {
        if pred_curr_att_duty_has_been_decided(s, id) 
        {
            var s_mod := f_update_process_after_att_duty_decided(
                                s,
                                id,
                                decided_attestation_data);

            lem_att_slashing_db_hist_cid_is_monotonic_f_check_for_next_duty(s_mod, s', cid);
        }            
    }         

    lemma lem_att_slashing_db_hist_cid_is_monotonic_f_listen_for_new_imported_blocks(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState,
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

        var s := f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                s,
                                block
                            );                    

        if pred_listen_for_new_imported_blocks_checker(s, att_consensus_instances_already_decided)
        {
            var decided_attestation_data := att_consensus_instances_already_decided[s.current_attestation_duty.safe_get().slot];
            var s := f_updateConsensusInstanceValidityCheck_in_listen_for_new_imported_blocks(
                                    s,
                                    att_consensus_instances_already_decided
                                );
            assert s' == f_check_for_next_duty(s).state;
            lem_att_slashing_db_hist_cid_is_monotonic_f_check_for_next_duty(s, s', cid);
        }
    }   

    lemma lem_att_slashing_db_hist_cid_is_monotonic_f_check_for_next_duty(
        s: DVCState,
        s': DVCState,
        cid: Slot
    )
    requires f_check_for_next_duty.requires(s)
    requires s' == f_check_for_next_duty(s).state
    requires cid in s.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures cid in s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures s.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys; 
    decreases s.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(s)    
        {
            
            if first_queued_att_duty_was_decided(s)
            {
                var s_mod := f_dequeue_attestation_duties_queue(s);
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_duty_updateConsensusInstanceValidityCheck5(
                    s.attestation_consensus_engine_state,
                    s_mod.attestation_slashing_db,
                    s_mod.attestation_consensus_engine_state,
                    cid
                );
                assert s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                lem_att_slashing_db_hist_cid_is_monotonic_f_check_for_next_duty(s_mod, s', cid);
                assert s.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys; 
            }
            else
            {
            }
        }
    }      

    lemma lem_att_slashing_db_hist_cid_is_monotonic(
        s: DVCState,
        event: Types.Event,
        s': DVCState,
        outputs: Outputs,
        cid: Slot       
    )
    requires DVC_Spec.Next.requires(s, event, s', outputs)
    requires DVC_Spec.Next(s, event, s', outputs)
    requires cid in s.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures cid in s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures s.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys;  
    {
        match event
        {
            case ServeAttstationDuty(attestation_duty) => 
                lem_att_slashing_db_hist_cid_is_monotonic_f_serve_attestation_duty(s, attestation_duty, s', cid);

            case AttConsensusDecided(id, decided_attestation_data) => 
                lem_att_slashing_db_hist_cid_is_monotonic_f_att_consensus_decided(s, id, decided_attestation_data, s', cid);
            
            case ReceivedAttestationShare(attestation_share) => 
                assert s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;

            case ImportedNewBlock(block) => 
                lem_att_slashing_db_hist_cid_is_monotonic_f_listen_for_new_imported_blocks(s, block, s', cid);
            
            case ResendAttestationShares => 
                assert s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
        
            case NoEvent => 
                assert s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;

        }           
    } 

    lemma lem_att_slashing_db_hist_cid_is_monotonic_corollary(
        s: DVCState,
        event: Types.Event,
        s': DVCState,
        outputs: Outputs,
        cid: Slot,
        vp: AttestationData -> bool       
    )
    requires DVC_Spec.Next.requires(s, event, s', outputs)    
    requires DVC_Spec.Next(s, event, s', outputs)
    requires cid in s.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    requires vp in s.attestation_consensus_engine_state.att_slashing_db_hist[cid]
    ensures cid in s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures vp in s'.attestation_consensus_engine_state.att_slashing_db_hist[cid]
    {
        lem_att_slashing_db_hist_cid_is_monotonic(s, event, s', outputs, cid);
    }          

    lemma lem_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_helper(
        s: DVState,
        event: DV.Event,
        cid: Slot,
        vp: AttestationData -> bool,
        hn: BLSPubkey,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_quorum_constraints(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)    
    requires hn in s.honest_nodes_states.Keys
    requires inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper_body(s, hn, s.honest_nodes_states[hn], cid)
    requires inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body(s, hn, s.honest_nodes_states[hn], cid, vp)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(s)
    requires inv_active_attestation_consensus_instances_predicate_is_in_att_slashing_db_hist_body(s.honest_nodes_states[hn], cid)
    ensures inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body(s', hn, s'.honest_nodes_states[hn], cid, vp)
    {
        // lem_inv_33_helper(s, event, cid, hn, s');
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>

                var s_w_honest_node_states_updated := lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_get_s_w_honest_node_states_updated(s, node, nodeEvent);           

                assert s_w_honest_node_states_updated.consensus_on_attestation_data == s.consensus_on_attestation_data;


                var output := 
                    if nodeEvent.AttConsensusDecided? && nodeEvent.id == cid then 
                        Some(Decided(node, nodeEvent.decided_attestation_data))
                    else
                        None
                    ;

                var validityPredicates := lem_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_helper_helper_function(s_w_honest_node_states_updated, cid);
                    // map n |
                    //         && n in s_w_honest_node_states_updated.honest_nodes_states.Keys 
                    //         && cid in s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
                    //     ::
                    //         s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances[cid].validityPredicate
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
                            lem_add_set_of_validity_predicates2(
                                s_consensus.honest_nodes_validity_functions, 
                                validityPredicates,
                                s'_consensus.honest_nodes_validity_functions,
                                hn,
                                vp
                            );
                            assert vp == s.honest_nodes_states[hn].attestation_consensus_engine_state.active_attestation_consensus_instances[cid].validityPredicate; 
                            assert vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[cid];
                        }
                    }
                    else 
                    {
                        assert hn in validityPredicates;
                        assert hn !in  s_consensus.honest_nodes_validity_functions.Keys;
                        // assert cid in s.honest_nodes_states[hn].attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;
                        // assert vp == s.honest_nodes_states[hn].attestation_consensus_engine_state.active_attestation_consensus_instances[cid].validityPredicate; 
                        
                        lem_add_set_of_validity_predicates3(
                            s_consensus.honest_nodes_validity_functions, 
                            validityPredicates,
                            s'_consensus.honest_nodes_validity_functions,
                            hn,
                            vp
                        );

                        assert vp == s.honest_nodes_states[hn].attestation_consensus_engine_state.active_attestation_consensus_instances[cid].validityPredicate; 
                        assert vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[cid];

                    }
                    assert vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[cid];

                    if hn == node 
                    {
                        lem_NextEvent_implies_NextHonestAfterAddingBlockToBn_and_DVC_Spec_Next(s, event, s');
                        assert DVC_Spec.Next(s_w_honest_node_states_updated.honest_nodes_states[hn], nodeEvent, s'.honest_nodes_states[hn], nodeOutputs);
                        lem_att_slashing_db_hist_cid_is_monotonic_corollary(s_w_honest_node_states_updated.honest_nodes_states[hn], nodeEvent, s'.honest_nodes_states[hn], nodeOutputs, cid, vp);
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
                    assert inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper_body(s, hn, s.honest_nodes_states[hn], cid);
                    assert cid in s.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                    assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                    assert cid in s'.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                    assert vp in s'.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist[cid];                 
                    
                } 

        }
    }  

    lemma lem_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_quorum_constraints(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)    
    requires inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist_helper(s)  
    requires inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(s) 
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(s)
    requires inv_active_attestation_consensus_instances_predicate_is_in_att_slashing_db_hist(s)
    ensures inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(s')   
    {
        forall hn: BLSPubkey, slot: Slot, vp : AttestationData -> bool |
            hn in s'.honest_nodes_states
        ensures inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body(s', hn, s'.honest_nodes_states[hn], slot, vp)    
        {
            lem_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_helper(s, event, slot, vp, hn, s');
        }
    }  

    lemma lemmaStartConsensusInstance(
        s: ConsensusEngineState,
        id: Slot,
        attestation_duty: AttestationDuty,
        attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState        
    ) 
    requires id !in s.active_attestation_consensus_instances.Keys 
    requires s' ==   startConsensusInstance(s, id, attestation_duty, attestation_slashing_db)
    ensures s'.att_slashing_db_hist.Keys == s.att_slashing_db_hist.Keys + {id}
    {    
    }

    lemma lemmaStartConsensusInstance2(
        s: ConsensusEngineState,
        id: Slot,
        attestation_duty: AttestationDuty,
        attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState        
    ) 
    requires id !in s.active_attestation_consensus_instances.Keys 
    requires s' ==   startConsensusInstance(s, id, attestation_duty, attestation_slashing_db)
    ensures s'.active_attestation_consensus_instances.Keys == s.active_attestation_consensus_instances.Keys + {id}
    // ensures s'.att_slashing_db_hist.Keys == s.att_slashing_db_hist.Keys + {id}
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
    requires id !in s.active_attestation_consensus_instances.Keys 
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
    requires id !in s.active_attestation_consensus_instances.Keys 
    requires id in s.att_slashing_db_hist.Keys
    requires s' ==   startConsensusInstance(s, id, attestation_duty, attestation_slashing_db)
    ensures id in s'.att_slashing_db_hist.Keys
    ensures s.att_slashing_db_hist[id].Keys <= s'.att_slashing_db_hist[id].Keys
    // ensures s'.att_slashing_db_hist[id] == {}
    {    
    } 

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state  
    requires index_next_attestation_duty_to_be_served > 0    
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)
    requires lem_ServeAttstationDuty2_predicate(dv, index_next_attestation_duty_to_be_served, attestation_duty, n)
    ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(dv, n, s', index_next_attestation_duty_to_be_served)
    {
        var new_p := f_enqueue_new_att_duty(
                            process,
                            attestation_duty
                        );

        lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_f_check_for_next_duty(new_p, s', dv, n, index_next_attestation_duty_to_be_served);
    }       

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(process, id, decided_attestation_data).state
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)    
    ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(dv, n, s', index_next_attestation_duty_to_be_served)
    {   
        if  pred_curr_att_duty_has_been_decided(process, id)
        {
            var s_mod := f_update_process_after_att_duty_decided(
                                process,
                                id,
                                decided_attestation_data);

            lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_f_check_for_next_duty(s_mod, s', dv, n, index_next_attestation_duty_to_be_served);     
        }
    }    

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        s': DVCState,
        dv': DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(dv', n, process, index_next_attestation_duty_to_be_served)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv', n, process, index_next_attestation_duty_to_be_served)    
    ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(dv', n, s', index_next_attestation_duty_to_be_served)
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var new_process :=
                f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                process,
                                block
                            );                       

        if pred_listen_for_new_imported_blocks_checker(new_process, att_consensus_instances_already_decided)
        {
            var s_mod := f_updateConsensusInstanceValidityCheck_in_listen_for_new_imported_blocks(
                                    new_process,
                                    att_consensus_instances_already_decided
                                );
                   
            lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_f_check_for_next_duty(s_mod, s', dv', n, index_next_attestation_duty_to_be_served);                    
        }        
    }        

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body_f_check_for_next_duty_helper(
        process: DVCState,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires s' == f_check_for_next_duty(process, attestation_duty).state  
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires first_queued_att_duty_was_decided_or_ready_to_be_served(process)    
    requires !first_queued_att_duty_was_decided(process)
    ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(dv, n, s', index_next_attestation_duty_to_be_served)
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
                        && var an := dv.sequence_attestation_duties_to_be_served[i];
                        && an.attestation_duty.slot == slot 
                        && an.node == n
                ;                                    
        {
            if slot in process.attestation_consensus_engine_state.att_slashing_db_hist
            {
                assert 
                    exists i: nat :: 
                        && i < index_next_attestation_duty_to_be_served
                        && var an := dv.sequence_attestation_duties_to_be_served[i];
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
                        && var an := dv.sequence_attestation_duties_to_be_served[i];
                        && an.attestation_duty.slot == slot 
                        && an.node == n
                ;                        
            }
        }
    }

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_f_check_for_next_duty(
        process: DVCState,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires s' == f_check_for_next_duty(process, attestation_duty).state  
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(dv, n, s', index_next_attestation_duty_to_be_served)
    decreases process.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(process)    
        {
            if first_queued_att_duty_was_decided(process)
            {
                var s_mod := f_dequeue_attestation_duties_queue(process);

                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_duty_updateConsensusInstanceValidityCheck(
                    process.attestation_consensus_engine_state,
                    s_mod.attestation_slashing_db,
                    s_mod.attestation_consensus_engine_state
                );

                assert s_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys == process.attestation_consensus_engine_state.att_slashing_db_hist.Keys;

                lem_f_check_for_next_duty_checker(process, s_mod);                 

                lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_f_check_for_next_duty(s_mod, s', dv, n, index_next_attestation_duty_to_be_served);
            }
            else 
            {        
                lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body_f_check_for_next_duty_helper(
                    process,
                    s',
                    dv,
                    n,
                    index_next_attestation_duty_to_be_served
                );
            }
        } 
        else 
        {
        }             
    }

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_helper_honest_helper4(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCState,
        n: BLSPubkey
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')      
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(s, n, s_node, s.index_next_attestation_duty_to_be_served)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s, n, s_node, s.index_next_attestation_duty_to_be_served)
    // requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(s_node)


    ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(s', n, s_node, s.index_next_attestation_duty_to_be_served)
    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', n, s_node, s.index_next_attestation_duty_to_be_served)
    {


        
    }       

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_helper_honest(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist(s)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(s)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b(s)    
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(s', event.node, s'.honest_nodes_states[event.node], s'.index_next_attestation_duty_to_be_served); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_helper_honest_helper4(s, event, s', s_node, node);

                assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);      
                assert inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(s_node);     

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lem_ServeAttstationDuty(s, event, s');
                        lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        lem_NonServeAttstationDuty(s, event, s');
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                        
               
                   
                    case ReceivedAttestationShare(attestation_share) =>
                        lem_NonServeAttstationDuty(s, event, s'); 
                        lem_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        // lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  
                        

                    case ImportedNewBlock(block) => 
                        lem_NonServeAttstationDuty(s, event, s');
                        var s_node2 := add_block_to_bn(s_node, nodeEvent.block);
                        lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                     
                    
                 
                    case ResendAttestationShares => 
                        lem_NonServeAttstationDuty(s, event, s');
                        lem_f_resend_attestation_share_constants(s_node, s'_node);
                        // lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  

                    case NoEvent => 
                        lem_NonServeAttstationDuty(s, event, s');
                        assert s_node == s'_node; 
                        // lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                          
                }                     

        }
    }   

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist(s)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(s)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b(s) 
    ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist(s');  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_helper_honest(s, event, s');
                   
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(s', hn, s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_helper_honest_helper4(s, event, s', s.honest_nodes_states[hn], hn);
                    }
                }  
                assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist(s');
                         
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(s', hn, s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served); 
                {
                    // if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_helper_honest_helper4(s, event, s', s.honest_nodes_states[hn], hn);
                    }
                }  
                assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist(s');            


        }
    }  

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state  
    requires index_next_attestation_duty_to_be_served > 0    
    requires inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv, n, process)
    requires inv_head_attetation_duty_queue_higher_than_latest_attestation_duty_body_body(process)
    requires inv_attestation_duty_queue_is_ordered_body_body(process) 
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)   
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_queued_att_duties_are_from_dv_seq_of_att_duties_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)
    requires is_sequence_attestation_duties_to_be_served_orderd(dv);
    requires lem_ServeAttstationDuty2_predicate(dv, index_next_attestation_duty_to_be_served, attestation_duty, n)
    ensures inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv, n, s')
    {
        var new_p := f_enqueue_new_att_duty(
                            process,
                            attestation_duty
                        );

        if process.attestation_duties_queue != []
        {
            assert inv_attestation_duty_queue_is_ordered_body_body(new_p); 
        }
        else 
        {
            assert inv_attestation_duty_queue_is_ordered_body_body(new_p); 
        }        

        lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a_f_check_for_next_duty(new_p, s', dv, n);
    }  

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(process, id, decided_attestation_data).state
    requires inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv, n, process)
    requires inv_head_attetation_duty_queue_higher_than_latest_attestation_duty_body_body(process)
    requires inv_attestation_duty_queue_is_ordered_body_body(process) 
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)   
    ensures inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv, n, s') 
    {    
        if  pred_curr_att_duty_has_been_decided(process, id)
        {
            var s_mod := f_update_process_after_att_duty_decided(
                                process,
                                id,
                                decided_attestation_data);

            lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a_f_check_for_next_duty(s_mod, s', dv, n);   
        }
    }        

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        s': DVCState,
        dv': DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv', n, process)
    requires inv_head_attetation_duty_queue_higher_than_latest_attestation_duty_body_body(process)
    requires inv_attestation_duty_queue_is_ordered_body_body(process) 
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)   
    ensures inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv', n, s')
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var new_process :=
                f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                process,
                                block
                            );                       

        if pred_listen_for_new_imported_blocks_checker(new_process, att_consensus_instances_already_decided)
        {
            var s_mod := f_updateConsensusInstanceValidityCheck_in_listen_for_new_imported_blocks(
                                    new_process,
                                    att_consensus_instances_already_decided
                                );
                   
            lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a_f_check_for_next_duty(s_mod, s', dv', n);                    
        }        
    }            

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a_f_check_for_next_duty(
        process: DVCState,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires s' == f_check_for_next_duty(process, attestation_duty).state  
    requires inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv, n, process)
    requires inv_head_attetation_duty_queue_higher_than_latest_attestation_duty_body_body(process)
    requires inv_attestation_duty_queue_is_ordered_body_body(process) 
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)   
    ensures inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv, n, s')
    decreases process.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(process)   
        {
            if first_queued_att_duty_was_decided(process)
            {
                var s_mod := f_dequeue_attestation_duties_queue(process);
           
                lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a_f_check_for_next_duty(
                    s_mod,
                    s',
                    dv,
                    n
                );

            }
            else 
            {       
                assert inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv, n, s'); 
            }
        } 
        else 
        {
        }             
    }  

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a_helper_honest_helper1(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCState,
        n: BLSPubkey
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')      
    requires inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s, n, s_node)
    ensures inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s', n, s_node)
    {

    }

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a_helper_honest_helper2(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')      
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s, n, s_node, index_next_attestation_duty_to_be_served)
    requires inv_queued_att_duties_are_from_dv_seq_of_att_duties_body_body(s, n, s_node, index_next_attestation_duty_to_be_served)
    requires is_sequence_attestation_duties_to_be_served_orderd(s);

    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', n, s_node, index_next_attestation_duty_to_be_served)
    ensures inv_queued_att_duties_are_from_dv_seq_of_att_duties_body_body(s', n, s_node, index_next_attestation_duty_to_be_served)
    ensures is_sequence_attestation_duties_to_be_served_orderd(s')
    {
        
    }    

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a_helper_honest(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a(s)
    requires inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(s)
    requires inv_attestation_duty_queue_is_ordered(s) 
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(s)   
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b(s)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_c(s)
    requires is_sequence_attestation_duties_to_be_served_orderd(s);    
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    ensures inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s', event.node, s'.honest_nodes_states[event.node]); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a_helper_honest_helper1(s, event, s', s_node, node);
                lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a_helper_honest_helper2(s, event, s', s_node, node, s.index_next_attestation_duty_to_be_served);

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lem_ServeAttstationDuty(s, event, s');
                        lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s', node, s'_node);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        lem_NonServeAttstationDuty(s, event, s');
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s', node, s'_node);                        
               
                   
                    case ReceivedAttestationShare(attestation_share) =>
                        lem_NonServeAttstationDuty(s, event, s'); 
                        lem_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        assert inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s', node, s'_node);  
                        

                    case ImportedNewBlock(block) => 
                        lem_NonServeAttstationDuty(s, event, s');
                        var s_node2 := add_block_to_bn(s_node, nodeEvent.block);
                        lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s', node, s'_node);                     
                    
                 
                    case ResendAttestationShares => 
                        lem_NonServeAttstationDuty(s, event, s');
                        lem_f_resend_attestation_share_constants(s_node, s'_node);
                        // lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s', node, s'_node);  

                    case NoEvent => 
                        lem_NonServeAttstationDuty(s, event, s');
                        assert s_node == s'_node; 
                        assert inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s', node, s'_node);                          
                }                     

        }
    }           

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a(s)
    requires inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(s)
    requires inv_attestation_duty_queue_is_ordered(s) 
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(s)   
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b(s)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_c(s)
    requires is_sequence_attestation_duties_to_be_served_orderd(s);
    ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a(s');  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a_helper_honest(s, event, s');
                   
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s', hn, s'.honest_nodes_states[hn]); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a_helper_honest_helper1(s, event, s', s.honest_nodes_states[hn], hn);
                    }
                }  
                assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a(s');
                         
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a_helper_honest(s, event, s');
                   
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s', hn, s'.honest_nodes_states[hn]); 
                {
                    // if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a_helper_honest_helper1(s, event, s', s.honest_nodes_states[hn], hn);
                    }
                }  
                assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a(s');            
         


        }
    }        

}