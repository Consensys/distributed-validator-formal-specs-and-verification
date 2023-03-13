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
include "invs_fnc_2.dfy"

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
    import opened Invs_DV_Next_1
    import opened Invs_DV_Next_2
    import opened Invs_DV_Next_3
    import opened Invs_DV_Next_4
    import opened Common_Proofs
    import opened DVC_Spec_Axioms
    import opened Helper_Pred_Fcn
    import opened Fnc_Invs_2
    import opened Helper_Sets_Lemmas

    lemma lem_att_slashing_db_hist_is_monotonic_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state  
    ensures process.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
    {
   
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
        }
    }      

    lemma lem_att_slashing_db_hist_is_monotonic_f_check_for_next_duty(
        s: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState
    )
    requires f_check_for_next_duty.requires(s, attestation_duty)
    requires s' == f_check_for_next_duty(s, attestation_duty).state
    ensures s.attestation_consensus_engine_state.att_slashing_db_hist.Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
    {
        
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
            case ServeAttestationDuty(attestation_duty) => 
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
    requires inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist_body(s, hn, s.honest_nodes_states[hn], cid)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(s)
    ensures inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist_body(s', hn, s'.honest_nodes_states[hn], cid)
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
                        assert inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist_body(s, hn, s.honest_nodes_states[hn], cid);

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

                         
            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) => 
                assert s'.consensus_on_attestation_data == s.consensus_on_attestation_data;
                assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                 
                if
                    && hn in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions.Keys
                {
                    assert inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist_body(s, hn, s.honest_nodes_states[hn], cid);
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
    requires inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist(s)   
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(s)
    ensures inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist(s')   
    {
        forall hn: BLSPubkey, slot: Slot |
            hn in s'.honest_nodes_states
        ensures inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist_body(s', hn, s'.honest_nodes_states[hn], slot)    
        {
            lem_inv_33_helper(s, event, slot, hn, s');
        }
    }  

    lemma lem_inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist_implies_46_a(dv: DVState)
    requires inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist(dv)
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
            assert inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist_body(dv, hn, hn_state, s);
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
    requires inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist(s)   
    requires inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(s)   
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(s)
    ensures inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(s')   
    {
        lem_inv_33(s, event, s');
        lem_inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist_implies_46_a(s');
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

    function lem_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body_helper_helper_function(
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
        }
    }   

    lemma lem_att_slashing_db_hist_cid_is_monotonic_f_check_for_next_duty(
        s: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState,
        cid: Slot
    )
    requires f_check_for_next_duty.requires(s, attestation_duty)
    requires s' == f_check_for_next_duty(s, attestation_duty).state
    requires cid in s.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures cid in s'.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    ensures s.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys; 
    {
        assert s.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys <= s'.attestation_consensus_engine_state.att_slashing_db_hist[cid].Keys; 
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
            case ServeAttestationDuty(attestation_duty) => 
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

    lemma lem_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body_HonestNodeTakingStep(
        s: DVState,
        event: DV.Event,
        cid: Slot,
        vp: AttestationData -> bool,
        hn: BLSPubkey,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires inv_quorum_constraints(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)    
    requires hn in s.honest_nodes_states.Keys
    requires inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist_body(s, hn, s.honest_nodes_states[hn], cid)
    requires inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body(s, hn, s.honest_nodes_states[hn], cid, vp)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(s)
    requires inv_active_attestation_consensus_instances_predicate_is_in_att_slashing_db_hist_body(s.honest_nodes_states[hn], cid)
    ensures inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body(s', hn, s'.honest_nodes_states[hn], cid, vp)
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

                var validityPredicates := lem_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body_helper_helper_function(s_w_honest_node_states_updated, cid);                    
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

                if && hn in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions.Keys
                   && vp in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions[hn]                          
                   && cid in hn'_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                {
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
        }
    }     

    lemma lem_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body_AdeversaryTakingStep(
        s: DVState,
        event: DV.Event,
        cid: Slot,
        vp: AttestationData -> bool,
        hn: BLSPubkey,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.AdeversaryTakingStep?
    requires inv_quorum_constraints(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)    
    requires hn in s.honest_nodes_states.Keys
    requires inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist_body(s, hn, s.honest_nodes_states[hn], cid)
    requires inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body(s, hn, s.honest_nodes_states[hn], cid, vp)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(s)
    requires inv_active_attestation_consensus_instances_predicate_is_in_att_slashing_db_hist_body(s.honest_nodes_states[hn], cid)
    ensures inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body(s', hn, s'.honest_nodes_states[hn], cid, vp)
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) => 
                assert s'.consensus_on_attestation_data == s.consensus_on_attestation_data;
                assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                 
                if
                    && hn in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions.Keys
                    && vp in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions[hn]                          
                    && cid in s'.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys
                {
                    assert inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist_body(s, hn, s.honest_nodes_states[hn], cid);
                    assert cid in s.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                    assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                    assert cid in s'.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                    assert vp in s'.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist[cid];                 
                } 

        }
    }  

    lemma lem_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body_helper(
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
    requires inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist_body(s, hn, s.honest_nodes_states[hn], cid)
    requires inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body(s, hn, s.honest_nodes_states[hn], cid, vp)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(s)
    requires inv_active_attestation_consensus_instances_predicate_is_in_att_slashing_db_hist_body(s.honest_nodes_states[hn], cid)
    ensures inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body(s', hn, s'.honest_nodes_states[hn], cid, vp)
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                lem_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body_HonestNodeTakingStep(
                    s,
                    event,
                    cid,
                    vp,
                    hn,
                    s'
                );
                
            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) => 
                lem_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body_AdeversaryTakingStep(
                    s,
                    event,
                    cid,
                    vp,
                    hn,
                    s'
                );
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
    requires inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist(s)  
    requires inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(s) 
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(s)
    requires inv_active_attestation_consensus_instances_predicate_is_in_att_slashing_db_hist(s)
    ensures inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(s')   
    {
        forall hn: BLSPubkey, slot: Slot, vp : AttestationData -> bool |
            hn in s'.honest_nodes_states
        ensures inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body(s', hn, s'.honest_nodes_states[hn], slot, vp)    
        {
            lem_inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body_helper(s, event, slot, vp, hn, s');
        }
    }  

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_f_terminate_current_attestation_duty(
        process: DVCState,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires s' == f_terminate_current_attestation_duty(process)
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(dv, n, process, index_next_attestation_duty_to_be_served)
    ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(dv, n, s', index_next_attestation_duty_to_be_served)
    {
        
    }

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_startConsensusInstance_helper(
        s: ConsensusEngineState,
        id: Slot,
        attestation_duty: AttestationDuty,
        attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState
    )
    requires startConsensusInstance.requires(s, id, attestation_duty, attestation_slashing_db)
    requires s' == startConsensusInstance(s, id, attestation_duty, attestation_slashing_db)
    ensures s.att_slashing_db_hist.Keys + { attestation_duty.slot } == s'.att_slashing_db_hist.Keys
    {   
        
    }

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_f_start_next_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_start_next_duty.requires(process, attestation_duty)
    requires s' == f_start_next_duty(process, attestation_duty).state  
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires pred_last_att_duty_is_delivering_to_given_honest_node(attestation_duty, dv, n, index_next_attestation_duty_to_be_served)
    ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(dv, n, s', index_next_attestation_duty_to_be_served)
    {
        lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_startConsensusInstance_helper(
            process.attestation_consensus_engine_state,
            attestation_duty.slot,
            attestation_duty,
            process.attestation_slashing_db,
            s'.attestation_consensus_engine_state
        );

        forall slot | slot in s'.attestation_consensus_engine_state.att_slashing_db_hist
        ensures exists i: Slot :: 
                    && i < index_next_attestation_duty_to_be_served
                    && var an := dv.sequence_attestation_duties_to_be_served[i];
                    && an.attestation_duty.slot == slot 
                    && an.node == n
                    ;
        {
            if slot in process.attestation_consensus_engine_state.att_slashing_db_hist
            {
                var i: Slot :| && i < index_next_attestation_duty_to_be_served
                               && var an := dv.sequence_attestation_duties_to_be_served[i];
                               && an.attestation_duty.slot == slot 
                               && an.node == n
                ;
            }
            else
            {
                assert slot == attestation_duty.slot;
                var i: Slot := index_next_attestation_duty_to_be_served - 1;
                var an := dv.sequence_attestation_duties_to_be_served[i];
                assert  && an.attestation_duty.slot == slot 
                        && an.node == n
                        ;
            }
        }
    }

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_updateConsensusInstanceValidityCheck_helper(
        s: ConsensusEngineState,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState
    )
    requires updateConsensusInstanceValidityCheck.requires(s, new_attestation_slashing_db)
    requires s' == updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db)
    ensures && var new_active_attestation_consensus_instances := 
                        updateConsensusInstanceValidityCheckHelper(
                            s.active_attestation_consensus_instances,
                            new_attestation_slashing_db
                        );
            && s.att_slashing_db_hist.Keys + new_active_attestation_consensus_instances.Keys == s'.att_slashing_db_hist.Keys
    {   

    }

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_f_check_for_next_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires s' == f_check_for_next_duty(process, attestation_duty).state  
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires pred_last_att_duty_is_delivering_to_given_honest_node(attestation_duty, dv, n, index_next_attestation_duty_to_be_served)
    ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(dv, n, s', index_next_attestation_duty_to_be_served)
    {   
        
        if attestation_duty.slot in process.future_att_consensus_instances_already_decided.Keys 
        {
            var new_attestation_slashing_db := 
                    f_update_attestation_slashing_db(
                        process.attestation_slashing_db, 
                        process.future_att_consensus_instances_already_decided[attestation_duty.slot]
                    );
            lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_updateConsensusInstanceValidityCheck_helper(
                    process.attestation_consensus_engine_state,
                    new_attestation_slashing_db,
                    s'.attestation_consensus_engine_state
            );
            assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(dv, n, s', index_next_attestation_duty_to_be_served);
        }
        else
        {
            lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_f_start_next_duty(
                process,
                attestation_duty,
                s',
                dv,
                n,
                index_next_attestation_duty_to_be_served
            );
            assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(dv, n, s', index_next_attestation_duty_to_be_served);
        }
            
    }

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_f_serve_attestation_duty(
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
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(dv, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)
    requires pred_last_att_duty_is_delivering_to_given_honest_node(attestation_duty, dv, n, index_next_attestation_duty_to_be_served)
    ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(dv, n, s', index_next_attestation_duty_to_be_served)
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});

        assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(dv, n, process_rcvd_duty, index_next_attestation_duty_to_be_served);

        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);

        lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_f_terminate_current_attestation_duty(
                process_rcvd_duty,
                process_after_stopping_active_consensus_instance,
                dv,
                n,
                index_next_attestation_duty_to_be_served
            );

        assert s' == f_check_for_next_duty(
                            process_after_stopping_active_consensus_instance,
                            attestation_duty
                        ).state;

        lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_f_check_for_next_duty(
                process_after_stopping_active_consensus_instance,
                attestation_duty,
                s',
                dv,
                n,
                index_next_attestation_duty_to_be_served
            );
    }       

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_f_att_consensus_decided(
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
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)
    ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(dv, n, s', index_next_attestation_duty_to_be_served)
    {   

    }    

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        s': DVCState,
        dv': DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(dv', n, process, index_next_attestation_duty_to_be_served)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)
    ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(dv', n, s', index_next_attestation_duty_to_be_served)
    {
        
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
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(s, n, s_node, s.index_next_attestation_duty_to_be_served)
    ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(s', n, s_node, s.index_next_attestation_duty_to_be_served)
    {

    }     

    lemma lem_inv_unchanged_dv_seq_of_att_duties_dv_next(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    ensures s.sequence_attestation_duties_to_be_served == s'.sequence_attestation_duties_to_be_served
    {

    }    

    lemma lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_helper_honest(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?    
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist(s)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(s)
    ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(s', event.node, s'.honest_nodes_states[event.node], s'.index_next_attestation_duty_to_be_served); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_helper_honest_helper4(s, event, s', s_node, node);

                assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(s_node);     

                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lem_ServeAttestationDuty(s, event, s');
                        lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        lem_NonServeAttestationDuty_unchanged_vars(s, event, s');
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                        
               
                    case ReceivedAttestationShare(attestation_share) =>
                        lem_NonServeAttestationDuty_unchanged_vars(s, event, s'); 
                        lem_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  
                        
                    case ImportedNewBlock(block) => 
                        lem_NonServeAttestationDuty_unchanged_vars(s, event, s');
                        var s_node2 := f_add_block_to_bn(s_node, nodeEvent.block);
                        lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                     
                 
                    case ResendAttestationShares => 
                        lem_NonServeAttestationDuty_unchanged_vars(s, event, s');
                        lem_f_resend_attestation_share_constants(s_node, s'_node);
                        assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  

                    case NoEvent => 
                        lem_NonServeAttestationDuty_unchanged_vars(s, event, s');
                        assert s_node == s'_node; 
                        assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                          
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
                ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(s', hn, s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_helper_honest_helper4(s, event, s', s.honest_nodes_states[hn], hn);
                    }
                }  
                assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist(s');
                         
            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body(s', hn, s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served); 
                {
                    assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                    lem_inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_helper_honest_helper4(s, event, s', s.honest_nodes_states[hn], hn);
                }  
                assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist(s');            
        }
    }  

    lemma lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty_f_terminate_current_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires s' == f_terminate_current_attestation_duty(process)
    requires index_next_attestation_duty_to_be_served > 0    
    requires inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv, n, process)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)   
    requires inv_sequence_attestation_duties_to_be_served_ordered(dv);
    ensures inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv, n, s')
    {
        
    }  

    lemma lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty_f_start_next_duty_helper(
        s: ConsensusEngineState,
        id: Slot,
        attestation_duty: AttestationDuty,
        attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState
    )
    requires startConsensusInstance.requires(s, id, attestation_duty, attestation_slashing_db)
    requires s' == startConsensusInstance(s, id, attestation_duty, attestation_slashing_db)
    ensures s.active_attestation_consensus_instances.Keys + { id } == s'.active_attestation_consensus_instances.Keys
    {
        
    }  

    lemma lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty_f_start_next_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_start_next_duty.requires(process, attestation_duty)
    requires s' == f_start_next_duty(process, attestation_duty).state
    requires index_next_attestation_duty_to_be_served > 0    
    requires inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv, n, process)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)   
    requires inv_sequence_attestation_duties_to_be_served_ordered(dv);
    ensures inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv, n, s')
    {
        lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty_f_start_next_duty_helper(
            process.attestation_consensus_engine_state,
            attestation_duty.slot,
            attestation_duty,
            process.attestation_slashing_db,
            s'.attestation_consensus_engine_state
        );
    }  

    lemma lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty_f_serve_attestation_duty(
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
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)   
    requires inv_sequence_attestation_duties_to_be_served_ordered(dv);
    ensures inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv, n, s')
    {
        
    }  

    lemma lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty_f_att_consensus_decided(
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
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)   
    ensures inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv, n, s') 
    {    
        
    }        

    lemma lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty_f_listen_for_new_imported_blocks(
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
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)   
    ensures inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv', n, s')
    {
             
    }            

    lemma lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty_f_check_for_next_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires s' == f_check_for_next_duty(process, attestation_duty).state  
    requires inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv, n, process)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)   
    ensures inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv, n, s')
    {
              
    }  

    lemma lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty_helper_honest_helper1(
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

    lemma lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty_helper_honest_helper2(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')      
    requires inv_sequence_attestation_duties_to_be_served_ordered(s);
    ensures inv_sequence_attestation_duties_to_be_served_ordered(s')
    {
        
    }    

    lemma lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_attestation_duty(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a(s)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(s)   
    requires inv_latest_attestation_duty_is_from_dv_seq_of_att_duties(s)
    requires inv_sequence_attestation_duties_to_be_served_ordered(s)
    requires inv_slot_of_consensus_instance_is_up_to_slot_of_latest_attestation_duty(s)
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    ensures inv_slot_of_consensus_instance_is_up_to_slot_of_latest_attestation_duty(s')
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s, event, s');
                
            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
        }
    }

    lemma lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a(s)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(s)   
    requires inv_latest_attestation_duty_is_from_dv_seq_of_att_duties(s)
    requires inv_sequence_attestation_duties_to_be_served_ordered(s);    
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
                lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty_helper_honest_helper1(s, event, s', s_node, node);
                lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty_helper_honest_helper2(s, event, s', s_node, node, s.index_next_attestation_duty_to_be_served);

                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lem_ServeAttestationDuty(s, event, s');
                        lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s', node, s'_node);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        lem_NonServeAttestationDuty_unchanged_vars(s, event, s');
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty_f_att_consensus_decided(
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
                        lem_NonServeAttestationDuty_unchanged_vars(s, event, s'); 
                        lem_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        assert inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s', node, s'_node);  
                        

                    case ImportedNewBlock(block) => 
                        lem_NonServeAttestationDuty_unchanged_vars(s, event, s');
                        var s_node2 := f_add_block_to_bn(s_node, nodeEvent.block);
                        lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s', node, s'_node);                     
                    
                 
                    case ResendAttestationShares => 
                        lem_NonServeAttestationDuty_unchanged_vars(s, event, s');
                        lem_f_resend_attestation_share_constants(s_node, s'_node);
                        // lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s', node, s'_node);  

                    case NoEvent => 
                        lem_NonServeAttestationDuty_unchanged_vars(s, event, s');
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
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(s)       
    requires inv_latest_attestation_duty_is_from_dv_seq_of_att_duties(s)
    requires inv_sequence_attestation_duties_to_be_served_ordered(s);
    ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a(s');  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s, event, s');
                   
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s', hn, s'.honest_nodes_states[hn]); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty_helper_honest_helper1(s, event, s', s.honest_nodes_states[hn], hn);
                    }
                }  
                assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a(s');
                         
            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>

        }
    }   
    
    lemma lem_inv_decided_data_has_an_honest_witness_add_block_to_bn_with_event(
        dv: DVState,
        node: BLSPubkey, 
        nodeEvent: Types.Event, 
        dv': DVState
    )    
    requires add_block_to_bn_with_event.requires(dv, node, nodeEvent)
    requires dv' == add_block_to_bn_with_event(dv, node, nodeEvent)
    requires inv_decided_data_has_an_honest_witness(dv)
    ensures  inv_decided_data_has_an_honest_witness(dv')
    {        
        
    }   

    lemma lem_inv_decided_data_has_an_honest_witness_ConsensusSpec_NextConsensusDecides<D(!new, 0)>(
        s: ConsensusInstance,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,        
        s': ConsensusInstance
    )    
    requires && ConsensusSpec.NextConsensusDecides.requires(s, honest_nodes_validity_predicates, s')
             && ConsensusSpec.NextConsensusDecides(s, honest_nodes_validity_predicates, s')
    requires inv_decided_data_has_an_honest_witness_body(s)
    requires isConditionForSafetyTrue(s)
    ensures  inv_decided_data_has_an_honest_witness_body(s')
    {

    }

    lemma lem_inv_decided_data_has_an_honest_witness_ConsensusSpec_Next<D(!new, 0)>(
        s: ConsensusInstance,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,        
        s': ConsensusInstance,
        output: Optional<OutCommand>
    )    
    requires && ConsensusSpec.Next.requires(s, honest_nodes_validity_predicates, s', output)
             && ConsensusSpec.Next(s, honest_nodes_validity_predicates, s', output)
    requires inv_decided_data_has_an_honest_witness_body(s)
    requires isConditionForSafetyTrue(s)
    ensures  inv_decided_data_has_an_honest_witness_body(s')
    {
        lem_inv_decided_data_has_an_honest_witness_ConsensusSpec_NextConsensusDecides(s, honest_nodes_validity_predicates, s');
    }

    lemma lem_inv_decided_data_has_an_honest_witness_ConsensusInstanceStep(
        dv: DVState,
        node: BLSPubkey, 
        nodeEvent: Types.Event, 
        nodeOutputs: Outputs,
        dv': DVState
    )    
    requires && DV.ConsensusInstanceStep.requires(dv, node, nodeEvent, nodeOutputs, dv')
             && DV.ConsensusInstanceStep(dv, node, nodeEvent, nodeOutputs, dv')
    requires inv_decided_data_has_an_honest_witness(dv)
    requires inv_consensus_instances_are_isConditionForSafetyTrue(dv)
    ensures  inv_decided_data_has_an_honest_witness(dv')
    {        
        forall cid | cid in dv.consensus_on_attestation_data.Keys 
        ensures inv_decided_data_has_an_honest_witness_body(dv'.consensus_on_attestation_data[cid])
        {
            assert isConditionForSafetyTrue(dv.consensus_on_attestation_data[cid]);

            var output := 
                if nodeEvent.AttConsensusDecided? && nodeEvent.id == cid then 
                    Some(Decided(node, nodeEvent.decided_attestation_data))
                else
                    None
                ;

            var validityPredicates := 
                map n |
                        && n in dv.honest_nodes_states.Keys 
                        && cid in dv.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
                    ::
                        dv.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances[cid].validityPredicate
                ;

            assert  ConsensusSpec.Next(
                        dv.consensus_on_attestation_data[cid],
                        validityPredicates,
                        dv'.consensus_on_attestation_data[cid],
                        output
                        );

            lem_inv_decided_data_has_an_honest_witness_ConsensusSpec_Next(
                dv.consensus_on_attestation_data[cid],
                validityPredicates,
                dv'.consensus_on_attestation_data[cid],
                output
                );
        }
            
    } 

    lemma lem_inv_decided_data_has_an_honest_witness_NextHonestAfterAddingBlockToBn(
        dv: DVState,
        node: BLSPubkey, 
        nodeEvent: Types.Event, 
        nodeOutputs: Outputs,
        dv': DVState
    )    
    requires && DV.NextHonestAfterAddingBlockToBn.requires(dv, node, nodeEvent, nodeOutputs, dv')
             && DV.NextHonestAfterAddingBlockToBn(dv, node, nodeEvent, nodeOutputs, dv')
    requires inv_decided_data_has_an_honest_witness(dv)
    requires inv_consensus_instances_are_isConditionForSafetyTrue(dv)
    ensures  inv_decided_data_has_an_honest_witness(dv')
    {        
        assert ConsensusInstanceStep(dv, node, nodeEvent, nodeOutputs, dv');
        lem_inv_decided_data_has_an_honest_witness_ConsensusInstanceStep(dv, node, nodeEvent, nodeOutputs, dv');
    } 

    lemma lem_inv_decided_data_has_an_honest_witness_NextHonestNode(
        dv: DVState,
        node: BLSPubkey, 
        nodeEvent: Types.Event, 
        nodeOutputs: Outputs,
        dv': DVState
    )    
    requires && DV.NextHonestNode.requires(dv, node, nodeEvent, nodeOutputs, dv')
             && DV.NextHonestNode(dv, node, nodeEvent, nodeOutputs, dv')
    requires inv_decided_data_has_an_honest_witness(dv)
    requires inv_consensus_instances_are_isConditionForSafetyTrue(dv)
    ensures  inv_decided_data_has_an_honest_witness(dv')
    {        
        assert node in dv.honest_nodes_states.Keys;
        var dv_w_honest_node_states_updated := add_block_to_bn_with_event(dv, node, nodeEvent);

        lem_inv_decided_data_has_an_honest_witness_add_block_to_bn_with_event(            
            dv, 
            node, 
            nodeEvent, 
            dv_w_honest_node_states_updated
            );

        assert NextHonestAfterAddingBlockToBn(dv_w_honest_node_states_updated, node, nodeEvent, nodeOutputs, dv');

        lem_inv_decided_data_has_an_honest_witness_NextHonestAfterAddingBlockToBn(
            dv_w_honest_node_states_updated, 
            node, 
            nodeEvent, 
            nodeOutputs, dv');
    }   

    lemma lem_inv_decided_data_has_an_honest_witness_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_decided_data_has_an_honest_witness(dv)
    requires inv_consensus_instances_are_isConditionForSafetyTrue(dv)
    ensures  inv_decided_data_has_an_honest_witness(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                lem_inv_decided_data_has_an_honest_witness_NextHonestNode(
                    dv,
                    node, 
                    nodeEvent, 
                    nodeOutputs,
                    dv'
                );    

            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                assert inv_decided_data_has_an_honest_witness(dv');
        }   
    }          

    lemma lem_inv_data_of_all_created_attestations_is_set_of_decided_values_dv_next(
        dv: DVState
    )    
    requires inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv)
    requires inv_data_of_att_share_is_decided_value(dv)
    requires inv_all_created_attestations_are_valid(dv)
    ensures  inv_data_of_all_created_attestations_is_set_of_decided_values(dv)
    {        
        forall a | a in dv.all_attestations_created && is_valid_attestation(a, dv.dv_pubkey)
        ensures && var consa := dv.consensus_on_attestation_data[a.data.slot];
                && consa.decided_value.isPresent() 
                && a.data == consa.decided_value.safe_get() 
        {
            var hn: BLSPubkey, att_share: AttestationShare 
                    :| 
                    inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(dv, hn, att_share, a);

            assert a.data.slot == att_share.data.slot;
            assert  inv_data_of_att_share_is_decided_value_body(dv, att_share);
            assert  && dv.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent()
                    && dv.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data
                    ;
        }
    }           

    lemma lem_inv_all_created_attestations_are_valid_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_only_dv_construct_signed_attestation_signature(dv)
    requires inv_all_created_attestations_are_valid(dv)
    ensures  inv_all_created_attestations_are_valid(dv')
    {        
        lem_inv_only_dv_construct_signed_attestation_signature_dv_next(dv, event, dv');
        assert inv_only_dv_construct_signed_attestation_signature(dv');

        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) =>     
                        lem_inv_outputs_attestations_submited_are_valid_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        if f_att_consensus_decided.requires(dvc, id, decided_attestation_data)
                        {
                            lem_inv_outputs_attestations_submited_are_valid_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');      
                        }                 
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_outputs_attestations_submited_are_valid_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_outputs_attestations_submited_are_valid_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendAttestationShares =>                         
                        
                    case NoEvent => 
                        
                }

                assert inv_outputs_attestations_submited_are_valid(nodeOutputs, dv.dv_pubkey);
                assert inv_all_created_attestations_are_valid(dv');

            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                assert NextAdversary(
                    dv,
                    node,
                    new_attestation_shares_sent,
                    messagesReceivedByTheNode,
                    dv'
                );
                
                var new_aggregated_attestations_sent := dv'.all_attestations_created - dv.all_attestations_created;

                forall aggregated_attestation_sent | aggregated_attestation_sent in new_aggregated_attestations_sent 
                ensures is_valid_attestation(aggregated_attestation_sent, dv.dv_pubkey)
                {
                    assert is_valid_attestation(aggregated_attestation_sent, dv.dv_pubkey);
                }
                                
                assert inv_all_created_attestations_are_valid(dv');
        }  
    }        

    lemma lem_pred_unchanged_rs_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    ensures ( forall hn: BLSPubkey | is_honest_node(dv, hn) ::
                    dv.honest_nodes_states[hn].rs.pubkey
                    ==
                    dv'.honest_nodes_states[hn].rs.pubkey
            )
    {

    }

    lemma lem_unique_owner_of_att_share(
        rs_pubkey: BLSPubkey,
        rs_pubkey': BLSPubkey,
        att_share: AttestationShare
    )
    requires pred_verify_owner_of_attestation_share_with_bls_signature(rs_pubkey, att_share)
    requires pred_verify_owner_of_attestation_share_with_bls_signature(rs_pubkey', att_share)
    ensures rs_pubkey == rs_pubkey'
    {
        var decided_attestation_data := att_share.data;
        var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
        var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
        assert verify_bls_signature(attestation_signing_root, att_share.signature, rs_pubkey);
        assert verify_bls_signature(attestation_signing_root, att_share.signature, rs_pubkey');
        rs_attestation_sign_and_verification_propeties();
        assert rs_pubkey == rs_pubkey';
    }

    lemma lem_inv_unchanged_dvc_rs_pubkey_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_unchanged_dvc_rs_pubkey(dv)
    ensures inv_unchanged_dvc_rs_pubkey(dv')
    {

    }

    lemma lem_different_signers_cannot_generate_the_same_att_share(
        rs_pubkey: BLSPubkey,
        rs_pubkey': BLSPubkey,
        att_share: AttestationShare
    )
    requires rs_pubkey != rs_pubkey'
    requires pred_verify_owner_of_attestation_share_with_bls_signature(rs_pubkey, att_share)
    ensures !pred_verify_owner_of_attestation_share_with_bls_signature(rs_pubkey', att_share)
    {
        if pred_verify_owner_of_attestation_share_with_bls_signature(rs_pubkey', att_share)
        {
            lem_unique_owner_of_att_share(rs_pubkey, rs_pubkey', att_share);
        }        
    }

    lemma lem_inv_honest_nodes_are_not_owner_of_att_shares_from_adversary(
        dv: DVState
    )
    requires inv_quorum_constraints(dv)
    ensures inv_honest_nodes_are_not_owner_of_att_shares_from_adversary(dv)
    {
        var honest_nodes := dv.honest_nodes_states.Keys;
        var dishonest_nodes := dv.adversary.nodes;
        lemmaEmptyIntersectionImpliesDisjointness(honest_nodes, dishonest_nodes);
        assert honest_nodes !! dishonest_nodes;

        forall byz_node: BLSPubkey, att_share: AttestationShare | 
            && byz_node in dv.adversary.nodes 
            && att_share in dv.att_network.allMessagesSent
            && pred_verify_owner_of_attestation_share_with_bls_signature(byz_node, att_share)
        ensures inv_honest_nodes_are_not_owner_of_att_shares_from_adversary_body(dv, att_share)
        {
            forall hn: BLSPubkey | is_honest_node(dv, hn)
            ensures !pred_verify_owner_of_attestation_share_with_bls_signature(hn, att_share)
            {
                assert hn != byz_node;
                lem_different_signers_cannot_generate_the_same_att_share(
                    byz_node,
                    hn,
                    att_share
                );
                assert !pred_verify_owner_of_attestation_share_with_bls_signature(hn, att_share);
            }
        }
    }

    lemma lem_inv_data_of_att_shares_is_known_dv_next_AdeversaryTakingStep(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.AdeversaryTakingStep?
    requires inv_quorum_constraints(dv)
    requires inv_data_of_att_shares_is_known(dv)
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_att_shares_to_broadcast_is_tracked_in_attestation_slashing_db(dv)
    ensures  inv_data_of_att_shares_is_known(dv')
    {        
        match event 
        {
            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                lem_inv_quorum_constraints_dv_next(dv, event, dv');
                assert inv_quorum_constraints(dv');
                var dishonest_nodes := dv'.adversary.nodes;
                var honest_nodes := dv'.honest_nodes_states.Keys;
                lemmaEmptyIntersectionImpliesDisjointness(dishonest_nodes, honest_nodes);
                assert dishonest_nodes !! honest_nodes;

                var new_att_shares := dv'.att_network.allMessagesSent - dv.att_network.allMessagesSent;
                forall new_att_share: AttestationShare, signer: BLSPubkey | 
                            (   && new_att_share in new_att_shares
                                && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(new_att_share.data.target.epoch));
                                && var attestation_signing_root := compute_attestation_signing_root(new_att_share.data, fork_version);
                                && verify_bls_signature(attestation_signing_root, new_att_share.signature, signer)
                            )
                ensures !is_honest_node(dv, signer)
                {
                    assert signer in dishonest_nodes;
                    assert !is_honest_node(dv, signer);
                }
                assert inv_data_of_att_shares_is_known(dv');
        }  
    } 

    lemma lem_inv_data_of_att_shares_is_known_dv_next_HonestNodeTakingStep(
        dv: DVState,
        event: DV.Event,
        dv': DVState,
        node: BLSPubkey, 
        nodeEvent: Types.Event, 
        nodeOutputs: Outputs
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.HonestNodeTakingStep?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires && var dvc' := dv'.honest_nodes_states[node];
             && inv_outputs_attestation_shares_sent_is_tracked_in_attestation_slashing_db(nodeOutputs, dvc');
    requires inv_quorum_constraints(dv)
    requires inv_data_of_att_shares_is_known(dv)
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_att_shares_to_broadcast_is_tracked_in_attestation_slashing_db(dv)
    ensures  inv_data_of_att_shares_is_known(dv')
    {        
        var dvc := dv.honest_nodes_states[node];
        var dvc' := dv'.honest_nodes_states[node];
        assert inv_outputs_attestation_shares_sent_is_tracked_in_attestation_slashing_db(nodeOutputs, dvc');

        assert  dv.att_network.allMessagesSent + getMessagesFromMessagesWithRecipient(nodeOutputs.att_shares_sent)
                ==
                dv'.att_network.allMessagesSent
                ;
        forall hn: BLSPubkey, att_share: AttestationShare | 
                    && is_honest_node(dv, hn)
                    && att_share in dv'.att_network.allMessagesSent 
                    && var hn_node': DVCState := dv'.honest_nodes_states[hn];
                    && var hn_rs_pubkey: BLSPubkey := hn_node'.rs.pubkey;
                    && pred_verify_owner_of_attestation_share_with_bls_signature(hn_rs_pubkey, att_share)
        ensures && var hn_node': DVCState := dv'.honest_nodes_states[hn];
                && inv_data_of_att_shares_is_known_body(hn_node', att_share)            
        {
            var hn_node: DVCState := dv.honest_nodes_states[hn];
            var hn_node': DVCState := dv'.honest_nodes_states[hn];
            var hn_rs_pubkey: BLSPubkey := hn_node'.rs.pubkey;

            lem_pred_unchanged_rs_dv_next(dv, event, dv');         
            assert hn_node.rs.pubkey == hn_node'.rs.pubkey;                    
            

            if att_share in dv.att_network.allMessagesSent 
            {
                assert inv_data_of_att_shares_is_known_body(hn_node, att_share);
                assert inv_data_of_att_shares_is_known_body(hn_node', att_share);
            }
            else
            {                        
                assert att_share in getMessagesFromMessagesWithRecipient(nodeOutputs.att_shares_sent);
                rs_attestation_sign_and_verification_propeties();
                assert inv_outputs_attestation_shares_sent_is_tracked_in_attestation_slashing_db_body(
                            dvc', 
                            att_share
                        );
                assert inv_data_of_att_shares_is_known_body(dvc', att_share);
                assert pred_verify_owner_of_attestation_share_with_bls_signature(dvc'.rs.pubkey, att_share);
                assert pred_verify_owner_of_attestation_share_with_bls_signature(hn_rs_pubkey, att_share);
                lem_unique_owner_of_att_share(hn_rs_pubkey, dvc'.rs.pubkey, att_share);
                assert hn_rs_pubkey == dvc'.rs.pubkey;

                calc 
                {
                    hn;
                    ==      
                    { lem_inv_unchanged_dvc_rs_pubkey_dv_next(dv, event, dv'); }
                    hn_rs_pubkey;
                    ==
                    dvc'.rs.pubkey;
                    ==
                    { lem_inv_unchanged_dvc_rs_pubkey_dv_next(dv, event, dv'); }
                    node;
                }

                assert hn_node' == dvc';
                assert inv_data_of_att_shares_is_known_body(hn_node', att_share);
            }
        }
        assert inv_data_of_att_shares_is_known(dv');
    }

    lemma lem_inv_data_of_att_shares_is_known_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_quorum_constraints(dv)
    requires inv_data_of_att_shares_is_known(dv)
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_att_shares_to_broadcast_is_tracked_in_attestation_slashing_db(dv)
    ensures  inv_data_of_att_shares_is_known(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) =>     
                        lem_inv_outputs_attestation_shares_sent_is_tracked_in_attestation_slashing_db_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv_outputs_attestation_shares_sent_is_tracked_in_attestation_slashing_db(nodeOutputs, dvc');  
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        if f_att_consensus_decided.requires(dvc, id, decided_attestation_data)
                        {
                            lem_inv_outputs_attestation_shares_sent_is_tracked_in_attestation_slashing_db_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');      
                            assert inv_outputs_attestation_shares_sent_is_tracked_in_attestation_slashing_db(nodeOutputs, dvc');  
                        }                 
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_outputs_attestation_shares_sent_is_tracked_in_attestation_slashing_db_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
                        assert inv_outputs_attestation_shares_sent_is_tracked_in_attestation_slashing_db(nodeOutputs, dvc');  
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_outputs_attestation_shares_sent_is_tracked_in_attestation_slashing_db_f_listen_for_new_imported_blocks(dvc, block, dvc');
                        assert inv_outputs_attestation_shares_sent_is_tracked_in_attestation_slashing_db(nodeOutputs, dvc');  
                                                
                    case ResendAttestationShares =>       
                        lem_inv_outputs_attestation_shares_sent_is_tracked_in_attestation_slashing_db_f_resend_attestation_share(dvc, dvc');
                        assert inv_outputs_attestation_shares_sent_is_tracked_in_attestation_slashing_db(nodeOutputs, dvc');                    
                        
                    case NoEvent => 
                        assert inv_outputs_attestation_shares_sent_is_tracked_in_attestation_slashing_db(nodeOutputs, dvc');  
                }
                
                assert inv_outputs_attestation_shares_sent_is_tracked_in_attestation_slashing_db(nodeOutputs, dvc');

                lem_inv_data_of_att_shares_is_known_dv_next_HonestNodeTakingStep(
                    dv,
                    event,
                    dv',
                    node, 
                    nodeEvent, 
                    nodeOutputs
                );

            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                lem_inv_data_of_att_shares_is_known_dv_next_AdeversaryTakingStep(
                    dv,
                    event,
                    dv'
                );
        }  
    }  

    lemma lem_inv_att_shares_to_broadcast_is_tracked_in_attestation_slashing_db_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_att_shares_to_broadcast_is_tracked_in_attestation_slashing_db(dv)
    ensures  inv_att_shares_to_broadcast_is_tracked_in_attestation_slashing_db(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) =>     
                        lem_inv_att_shares_to_broadcast_is_tracked_in_attestation_slashing_db_body_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        if f_att_consensus_decided.requires(dvc, id, decided_attestation_data)
                        {
                            lem_inv_att_shares_to_broadcast_is_tracked_in_attestation_slashing_db_body_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');      
                        }                 
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_att_shares_to_broadcast_is_tracked_in_attestation_slashing_db_body_f_listen_for_attestation_shares(dvc, attestation_share, dvc');         
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_att_shares_to_broadcast_is_tracked_in_attestation_slashing_db_body_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendAttestationShares =>       
                        
                    case NoEvent => 
                }
                
            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
        }  
    }  

    lemma lem_AdeversaryTakingStep_new_att_share_sent_is_not_from_honest_node(
        dv: DVState,        
        event: DV.Event,
        node: BLSPubkey,
        new_attestation_shares_sent: set<MessaageWithRecipient<AttestationShare>>,
        messagesReceivedByTheNode: set<AttestationShare>,
        dv': DVState,
        pubkey: BLSPubkey,
        new_att_share_sent: MessaageWithRecipient<AttestationShare>
    )
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv') 
    requires event.AdeversaryTakingStep? 
    requires NextAdversary(dv, node, new_attestation_shares_sent, messagesReceivedByTheNode, dv')
    requires inv_quorum_constraints(dv)
    requires && new_att_share_sent in new_attestation_shares_sent
             && pred_verify_owner_of_attestation_share_with_bls_signature(pubkey, new_att_share_sent.message)
    ensures !is_honest_node(dv', pubkey)
    {
        var message := new_att_share_sent.message;
        var att_data := message.data;

        lem_inv_quorum_constraints_dv_next(dv, event, dv');
        assert inv_quorum_constraints(dv');
        var dishonest_nodes := dv'.adversary.nodes;
        var honest_nodes := dv'.honest_nodes_states.Keys;
        lemmaEmptyIntersectionImpliesDisjointness(dishonest_nodes, honest_nodes);
        assert dishonest_nodes !! honest_nodes;

        var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_data.target.epoch));
        var attestation_signing_root := compute_attestation_signing_root(att_data, fork_version);
        assert verify_bls_signature(attestation_signing_root, message.signature, pubkey);

        assert pubkey in dishonest_nodes;
        assert !is_honest_node(dv, pubkey);
    }

    lemma lem_AdeversaryTakingStep_att_share_from_honest_node_were_sent_before(
        dv: DVState,        
        event: DV.Event,
        node: BLSPubkey,
        new_attestation_shares_sent: set<MessaageWithRecipient<AttestationShare>>,
        messagesReceivedByTheNode: set<AttestationShare>,
        dv': DVState,
        pubkey: BLSPubkey,
        old_att_share: AttestationShare
    )
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv') 
    requires event.AdeversaryTakingStep? 
    requires NextAdversary(dv, node, new_attestation_shares_sent, messagesReceivedByTheNode, dv')
    requires inv_quorum_constraints(dv)
    requires is_honest_node(dv', pubkey)
    requires && old_att_share in dv'.att_network.allMessagesSent
             && pred_verify_owner_of_attestation_share_with_bls_signature(pubkey, old_att_share)
    ensures old_att_share in dv.att_network.allMessagesSent
    {
        var att_data := old_att_share.data;
        var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_data.target.epoch));
        var attestation_signing_root := compute_attestation_signing_root(att_data, fork_version);
        
        assert  dv'.att_network.allMessagesSent
                == 
                dv.att_network.allMessagesSent + getMessagesFromMessagesWithRecipient(new_attestation_shares_sent);

        assert  || old_att_share in dv.att_network.allMessagesSent
                || old_att_share in getMessagesFromMessagesWithRecipient(new_attestation_shares_sent)
                ;

        if old_att_share in getMessagesFromMessagesWithRecipient(new_attestation_shares_sent)
        {
            if new_attestation_shares_sent == {}
            {
                assert {} == getMessagesFromMessagesWithRecipient(new_attestation_shares_sent);
            }
            assert {} != getMessagesFromMessagesWithRecipient(new_attestation_shares_sent);
            var old_att_share_sent :|
                    && old_att_share_sent in new_attestation_shares_sent
                    && old_att_share_sent.message == old_att_share
                    ;
            var signer: BLSPubkey :| verify_bls_signature(attestation_signing_root, old_att_share.signature, signer);
            assert signer in dv'.adversary.nodes;     
            lem_inv_honest_nodes_are_not_owner_of_att_shares_from_adversary(dv');
            lem_different_signers_cannot_generate_the_same_att_share(
                signer,
                pubkey,
                old_att_share
            );
        }
        assert old_att_share !in getMessagesFromMessagesWithRecipient(new_attestation_shares_sent);
        assert old_att_share in dv.att_network.allMessagesSent;
    }

    lemma lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_dv_next_AdeversaryTakingStep(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.AdeversaryTakingStep?
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_quorum_constraints(dv)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(dv)
    requires inv_data_of_att_shares_is_known(dv)
    requires inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv)
    requires inv_slot_of_consensus_instance_is_up_to_slot_of_latest_attestation_duty(dv)
    requires inv_available_current_att_duty_is_latest_served_att_duty(dv)
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a(dv)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(dv)   
    requires inv_latest_attestation_duty_is_from_dv_seq_of_att_duties(dv)
    requires inv_sequence_attestation_duties_to_be_served_ordered(dv)
    ensures  inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv')
    {        
        
        match event 
        {
            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                lem_inv_unchanged_dvc_rs_pubkey_dv_next(dv, event, dv');
        
                forall hn: BLSPubkey, slot: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation> | 
                            && is_honest_node(dv, hn) 
                            && var dvc' := dv.honest_nodes_states[hn];
                            && slot in dvc'.attestation_consensus_engine_state.att_slashing_db_hist
                            && vp in dvc'.attestation_consensus_engine_state.att_slashing_db_hist[slot]
                            && db in dvc'.attestation_consensus_engine_state.att_slashing_db_hist[slot][vp]
                ensures inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_body(
                            dv',
                            hn,
                            slot,
                            vp,
                            db)
                {
                    var dvc := dv.honest_nodes_states[hn];
                    var dvc' := dv'.honest_nodes_states[hn];
                    assert dvc == dvc';
                    assert db in dvc.attestation_consensus_engine_state.att_slashing_db_hist[slot][vp];

                    assert inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_body(
                            dv,
                            hn,
                            slot, 
                            vp, 
                            db
                        );
                    
                    assert hn == dvc.rs.pubkey;

                    forall att_share: AttestationShare | 
                            && att_share in dv'.att_network.allMessagesSent
                            && is_honest_node(dv', hn)
                            && pred_verify_owner_of_attestation_share_with_bls_signature(hn, att_share)
                            && att_share.data.slot < slot
                    ensures &&  var att_data := att_share.data;
                            && var slashing_db_attestation := SlashingDBAttestation(
                                            source_epoch := att_data.source.epoch,
                                            target_epoch := att_data.target.epoch,
                                            signing_root := Some(hash_tree_root(att_data)));
                            && slashing_db_attestation in db
                    {
                        lem_AdeversaryTakingStep_att_share_from_honest_node_were_sent_before(
                            dv,        
                            event,
                            node,
                            new_attestation_shares_sent,
                            messagesReceivedByTheNode,
                            dv',
                            hn,
                            att_share
                        );
                        assert att_share in dv.att_network.allMessagesSent;

                        var att_data := att_share.data;
                        var slashing_db_attestation := SlashingDBAttestation(
                                            source_epoch := att_data.source.epoch,
                                            target_epoch := att_data.target.epoch,
                                            signing_root := Some(hash_tree_root(att_data)));

                        assert  && att_share in dv.att_network.allMessagesSent
                                && is_honest_node(dv, hn)
                                && pred_verify_owner_of_attestation_share_with_bls_signature(hn, att_share)
                                && att_share.data.slot < slot
                                ;
                        assert slashing_db_attestation in db;                        
                    }
                    
                }

                assert inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv');
            
        }  
    }    

    lemma lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_dv_next_AttConsensusDecided(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.HonestNodeTakingStep?
    requires event.event.AttConsensusDecided?
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_quorum_constraints(dv)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(dv)
    requires inv_data_of_att_shares_is_known(dv)
    requires inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv)
    requires inv_slot_of_consensus_instance_is_up_to_slot_of_latest_attestation_duty(dv)
    requires inv_available_current_att_duty_is_latest_served_att_duty(dv)
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a(dv)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(dv)   
    requires inv_latest_attestation_duty_is_from_dv_seq_of_att_duties(dv)
    requires inv_sequence_attestation_duties_to_be_served_ordered(dv)
    ensures  inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv')
    {        
        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        if f_att_consensus_decided.requires(dvc, id, decided_attestation_data)
                        {
                            if  is_decided_data_for_current_slot(dvc, decided_attestation_data, id)
                            {
                                var allMessagesSent := dv.att_network.allMessagesSent;
                                
                                lem_inv_slot_of_consensus_instance_is_up_to_slot_of_latest_attestation_duty(
                                    dv,
                                    event,
                                    dv'
                                );

                                assert ( forall slot  |
                                                    slot in dvc'.attestation_consensus_engine_state.att_slashing_db_hist
                                                    ::
                                                    slot <= dvc'.latest_attestation_duty.safe_get().slot
                                        );
                                lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_dvc_f_att_consensus_decided_new_att_shares_sent(
                                            allMessagesSent,
                                            dvc,
                                            id,
                                            decided_attestation_data, 
                                            dvc'
                                        );
                                
                                var allMessagesSent' := dv'.att_network.allMessagesSent;
                                var outputs := f_att_consensus_decided(dvc, id, decided_attestation_data).outputs;
                                assert allMessagesSent' == allMessagesSent + getMessagesFromMessagesWithRecipient(outputs.att_shares_sent);

                                var attestation_with_signature_share := f_calc_att_with_sign_share_from_decided_att_data(
                                                                        dvc,
                                                                        id,
                                                                        decided_attestation_data
                                                                    );       
                                var messagesToBeSent := f_att_consensus_decided(dvc, id, decided_attestation_data).outputs.att_shares_sent;

                                assert forall m | m in messagesToBeSent :: m.message == attestation_with_signature_share; 

                                lemmaOnGetMessagesFromMessagesWithRecipientWhenAllMessagesAreTheSame(messagesToBeSent, attestation_with_signature_share);    
                                assert getMessagesFromMessagesWithRecipient(messagesToBeSent) ==  {attestation_with_signature_share};
                                assert  dv'.att_network.allMessagesSent 
                                        == 
                                        dv.att_network.allMessagesSent + { attestation_with_signature_share }
                                        ; 

                                forall hn: BLSPubkey, slot: Slot, vp: AttestationData -> bool, db: set<SlashingDBAttestation> | 
                                            && is_honest_node(dv, hn) 
                                            && var process' := dv.honest_nodes_states[hn];
                                            && slot in process'.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                                            && vp in process'.attestation_consensus_engine_state.att_slashing_db_hist[slot]
                                            && db in process'.attestation_consensus_engine_state.att_slashing_db_hist[slot][vp]
                                ensures inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_body(
                                            dv',
                                            hn,
                                            slot,
                                            vp,
                                            db)
                                {
                                    var process := dv.honest_nodes_states[hn];
                                    var process' := dv'.honest_nodes_states[hn];                            
                                    assert hn == process.rs.pubkey == process'.rs.pubkey;

                                    forall att_share: AttestationShare | 
                                            && att_share in dv'.att_network.allMessagesSent
                                            && is_honest_node(dv', hn)
                                            && pred_verify_owner_of_attestation_share_with_bls_signature(hn, att_share)
                                            && att_share.data.slot < slot
                                    ensures && var att_data := att_share.data;
                                            && var slashing_db_attestation := SlashingDBAttestation(
                                                            source_epoch := att_data.source.epoch,
                                                            target_epoch := att_data.target.epoch,
                                                            signing_root := Some(hash_tree_root(att_data)));
                                            && slashing_db_attestation in db
                                    {
                                        assert  || att_share in dv.att_network.allMessagesSent 
                                                || att_share in { attestation_with_signature_share }
                                                ;
                                        if att_share in dv.att_network.allMessagesSent
                                        {
                                            var att_data := att_share.data;
                                            var slashing_db_attestation := SlashingDBAttestation(
                                                                source_epoch := att_data.source.epoch,
                                                                target_epoch := att_data.target.epoch,
                                                                signing_root := Some(hash_tree_root(att_data)));

                                            assert  && att_share in dv.att_network.allMessagesSent
                                                    && is_honest_node(dv, hn)
                                                    && pred_verify_owner_of_attestation_share_with_bls_signature(hn, att_share)
                                                    && att_share.data.slot < slot
                                                    ;
                                            assert slashing_db_attestation in db;                        
                                        }
                                        else
                                        {
                                            assert att_share == attestation_with_signature_share;

                                            var att_data := att_share.data;
                                            var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_data.target.epoch));
                                            var attestation_signing_root := compute_attestation_signing_root(att_data, fork_version);
                                            var signer: BLSPubkey :| 
                                                    verify_bls_signature(attestation_signing_root, att_share.signature, signer);

                                            assert pred_verify_owner_of_attestation_share_with_bls_signature(dvc'.rs.pubkey, attestation_with_signature_share);

                                            lem_unique_owner_of_att_share(
                                                signer,
                                                dvc'.rs.pubkey,
                                                attestation_with_signature_share
                                            );
                                            assert signer == dvc'.rs.pubkey;
                                            if hn == signer
                                            {
                                                assert ( forall slot: Slot | slot in dvc'.attestation_consensus_engine_state.att_slashing_db_hist ::
                                                        attestation_with_signature_share.data.slot >= slot
                                                );
                                            }
                                            else
                                            {
                                                lem_different_signers_cannot_generate_the_same_att_share(
                                                    dvc'.rs.pubkey,
                                                    hn,
                                                    attestation_with_signature_share
                                                );

                                                assert !pred_verify_owner_of_attestation_share_with_bls_signature(hn, attestation_with_signature_share);
                                            }

                                        }
                                    }
                                    
                                }
                                        
                            }
                            else
                            {
                                assert inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv');
                            }

                        }                 
                        assert inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv');        
                }                                                
        }  
    }   

    lemma lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_dv_next_ServeAttestationDuty(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.HonestNodeTakingStep?
    requires event.event.ServeAttestationDuty?
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_quorum_constraints(dv)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(dv)
    requires inv_data_of_att_shares_is_known(dv)
    requires inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv)
    requires inv_slot_of_consensus_instance_is_up_to_slot_of_latest_attestation_duty(dv)
    requires inv_available_current_att_duty_is_latest_served_att_duty(dv)
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a(dv)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(dv)   
    requires inv_latest_attestation_duty_is_from_dv_seq_of_att_duties(dv)
    requires inv_sequence_attestation_duties_to_be_served_ordered(dv)
    ensures  inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv')
    {        
        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) =>  
                        lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_dvc_f_serve_attestation_duty(
                            dv.att_network.allMessagesSent,
                            dvc,
                            attestation_duty,
                            dvc'
                        );
                        assert inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv');
                }
        }
    }

    lemma lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_dv_next_ImportedNewBlock(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.HonestNodeTakingStep?
    requires event.event.ImportedNewBlock?
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_quorum_constraints(dv)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(dv)
    requires inv_data_of_att_shares_is_known(dv)
    requires inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv)
    requires inv_slot_of_consensus_instance_is_up_to_slot_of_latest_attestation_duty(dv)
    requires inv_available_current_att_duty_is_latest_served_att_duty(dv)
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a(dv)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(dv)   
    requires inv_latest_attestation_duty_is_from_dv_seq_of_att_duties(dv)
    requires inv_sequence_attestation_duties_to_be_served_ordered(dv)
    ensures  inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv')
    {        
        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_dvc_f_listen_for_new_imported_blocks(
                            dv.att_network.allMessagesSent,
                            dvc,
                            block,
                            dvc'
                        );
                        assert inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv');
                }
        }
    }

    lemma lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_dv_next_ResendAttestationShares(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.HonestNodeTakingStep?
    requires event.event.ResendAttestationShares?
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_quorum_constraints(dv)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(dv)
    requires inv_data_of_att_shares_is_known(dv)
    requires inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv)
    requires inv_slot_of_consensus_instance_is_up_to_slot_of_latest_attestation_duty(dv)
    requires inv_available_current_att_duty_is_latest_served_att_duty(dv)
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a(dv)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(dv)   
    requires inv_latest_attestation_duty_is_from_dv_seq_of_att_duties(dv)
    requires inv_sequence_attestation_duties_to_be_served_ordered(dv)
    ensures  inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv')
    {        
        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ResendAttestationShares =>           
                        lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_dvc_f_resend_attestation_share(
                            dv.att_network.allMessagesSent,
                            dvc,
                            dvc'
                        );
                        assert  dv.att_network.allMessagesSent == dv'.att_network.allMessagesSent;
                        assert  inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_dvc(                
                                    dv'.att_network.allMessagesSent,
                                    dvc'
                                );
                        assert  inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv');
                }
        }
    }

    lemma lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_quorum_constraints(dv)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(dv)
    requires inv_data_of_att_shares_is_known(dv)
    requires inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv)
    requires inv_slot_of_consensus_instance_is_up_to_slot_of_latest_attestation_duty(dv)
    requires inv_available_current_att_duty_is_latest_served_att_duty(dv)
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a(dv)
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(dv)   
    requires inv_latest_attestation_duty_is_from_dv_seq_of_att_duties(dv)
    requires inv_sequence_attestation_duties_to_be_served_ordered(dv)
    ensures  inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv')
    {        
        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) =>  
                        lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_dv_next_ServeAttestationDuty(
                            dv,
                            event,
                            dv'
                        );
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_dv_next_AttConsensusDecided(
                            dv,
                            event,
                            dv'
                        );
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        assert inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv');

                    case ImportedNewBlock(block) => 
                        lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_dv_next_ImportedNewBlock(
                            dv,
                            event,
                            dv'
                        );
                                                
                    case ResendAttestationShares =>           
                        lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_dv_next_ResendAttestationShares(
                            dv,
                            event,
                            dv'
                        );
                        
                    case NoEvent =>                         
                        assert  inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv');
                }

            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                lem_inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_dv_next_AdeversaryTakingStep(
                            dv,
                            event,
                            dv'
                        );
        }  
    }    

    lemma lem_inv_attestation_is_created_with_shares_from_quorum_dv_next_AdeversaryTakingStep(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.AdeversaryTakingStep?
    requires inv_only_dv_construct_signed_attestation_signature(dv)
    requires invNetwork(dv)
    requires inv_rcvd_attestation_shares_is_in_all_messages_sent(dv)
    requires inv_attestation_is_created_with_shares_from_quorum(dv)
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_attestation_is_created_with_shares_from_quorum(dv)
    ensures  inv_attestation_is_created_with_shares_from_quorum(dv')
    {        
        lem_inv_only_dv_construct_signed_attestation_signature_dv_next(dv, event, dv');
        assert inv_only_dv_construct_signed_attestation_signature(dv');

        lem_inv_unchanged_dvc_rs_pubkey_dv_next(dv, event, dv');
        assert ( forall hn: BLSPubkey | is_honest_node(dv, hn) ::
                        && hn == dv.honest_nodes_states[hn].rs.pubkey
                        && hn == dv'.honest_nodes_states[hn].rs.pubkey
        );

        lem_inv_rcvd_attestation_shares_is_in_all_messages_sent(dv, event, dv');

        match event 
        {
            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                assert NextAdversary(
                    dv,
                    node,
                    new_attestation_shares_sent,
                    messagesReceivedByTheNode,
                    dv'
                );
                
                var new_aggregated_attestations_sent := dv'.all_attestations_created - dv.all_attestations_created;

                forall aggregated_attestation_sent | aggregated_attestation_sent in new_aggregated_attestations_sent 
                ensures inv_attestation_is_created_with_shares_from_quorum_body(dv', aggregated_attestation_sent)
                {
                    assert inv_attestation_is_created_with_shares_from_quorum_body(dv', aggregated_attestation_sent);
                }
                                
                assert inv_attestation_is_created_with_shares_from_quorum(dv');
        }  
    } 

    lemma lem_inv_attestation_is_created_with_shares_from_quorum_dv_next_HonestNodeTakingStep(
        dv: DVState,
        event: DV.Event,
        dv': DVState,
        node: BLSPubkey, 
        nodeEvent: Types.Event, 
        nodeOutputs: Outputs
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.HonestNodeTakingStep?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires && var dvc' := dv'.honest_nodes_states[node];
             && inv_outputs_attestations_submited_is_created_with_shares_from_quorum(
                    nodeOutputs,
                    dvc'
                )
             
    requires inv_only_dv_construct_signed_attestation_signature(dv)
    requires inv_only_dv_construct_signed_attestation_signature(dv')
    requires ( forall hn: BLSPubkey | is_honest_node(dv, hn) ::
                        && hn == dv.honest_nodes_states[hn].rs.pubkey
                        && hn == dv'.honest_nodes_states[hn].rs.pubkey
            );
    requires inv_rcvd_attestation_shares_is_in_all_messages_sent(dv')    
    requires invNetwork(dv)
    requires inv_rcvd_attestation_shares_is_in_all_messages_sent(dv)
    requires inv_attestation_is_created_with_shares_from_quorum(dv)
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_attestation_is_created_with_shares_from_quorum(dv)
    ensures  inv_attestation_is_created_with_shares_from_quorum(dv')
    {        
        var dvc := dv.honest_nodes_states[node];
        var dvc' := dv'.honest_nodes_states[node];

        assert inv_outputs_attestations_submited_is_created_with_shares_from_quorum(nodeOutputs, dvc');
        assert dv'.all_attestations_created == dv.all_attestations_created + nodeOutputs.attestations_submitted;

        forall att: Attestation | att in dv'.all_attestations_created 
        ensures inv_attestation_is_created_with_shares_from_quorum_body(dv', att)
        {
            if att in dv.all_attestations_created 
            {
                assert inv_attestation_is_created_with_shares_from_quorum_body(dv, att);
                var att_shares, dvc_signer_pubkeys :|
                        && att_shares <= dv.att_network.allMessagesSent
                        && var constructed_sig := dv.construct_signed_attestation_signature(att_shares);
                        && constructed_sig.isPresent()
                        && constructed_sig.safe_get() == att.signature
                        && all_att_shares_have_the_same_data(att_shares, att.data)
                        && dvc_signer_pubkeys <= dv.all_nodes
                        && inv_attestation_is_created_with_shares_from_quorum_body_signers(dv, att_shares, dvc_signer_pubkeys)
                        && |dvc_signer_pubkeys| >= quorum(|dv.all_nodes|)
                        && dvc_signer_pubkeys <= dv.all_nodes
                        ;
                var constructed_sig := dv.construct_signed_attestation_signature(att_shares);

                assert dv.att_network.allMessagesSent <= dv'.att_network.allMessagesSent;
                assert att_shares <= dv'.att_network.allMessagesSent;

                lem_inv_only_dv_construct_signed_attestation_signature_dv_next(dv, event, dv');                        
                assert constructed_sig == dv'.construct_signed_attestation_signature(att_shares);
                assert dvc_signer_pubkeys <= dv'.all_nodes;
                assert inv_attestation_is_created_with_shares_from_quorum_body_signers(dv', att_shares, dvc_signer_pubkeys);
                assert inv_attestation_is_created_with_shares_from_quorum_body(dv', att);
            }
            else
            {
                assert att in nodeOutputs.attestations_submitted;
                assert inv_outputs_attestations_submited_is_created_with_shares_from_quorum_body(dvc', att);
                var att_shares, rs_signer_pubkeys, k :|        
                            && k in dvc'.rcvd_attestation_shares[att.data.slot].Keys
                            && att_shares <= dvc'.rcvd_attestation_shares[att.data.slot][k]
                            && var constructed_sig := dvc'.construct_signed_attestation_signature(att_shares);
                            && constructed_sig.isPresent()
                            && constructed_sig.safe_get() == att.signature
                            && all_att_shares_have_the_same_data(att_shares, att.data)
                            && inv_attestation_is_created_with_shares_from_quorum_rs_signers(att_shares, rs_signer_pubkeys)
                            && |rs_signer_pubkeys| >= quorum(|dvc'.peers|)
                            && rs_signer_pubkeys <= dvc'.peers
                            ;
                var constructed_sig := dvc'.construct_signed_attestation_signature(att_shares);

                assert  dvc'.peers == dv'.all_nodes;
                assert  quorum(|dvc'.peers|) == quorum(|dv'.all_nodes|);
                assert  && |rs_signer_pubkeys| >= quorum(|dvc'.peers|)
                        && rs_signer_pubkeys <= dv'.all_nodes;

                

                lem_inv_only_dv_construct_signed_attestation_signature_dv_next(dv, event, dv');                        
                assert constructed_sig == dv'.construct_signed_attestation_signature(att_shares);
                assert inv_attestation_is_created_with_shares_from_quorum_body_signers(dv', att_shares, rs_signer_pubkeys);

                lem_inv_rcvd_attestation_shares_is_in_all_messages_sent(dv, event, dv');  
                assert dvc'.rcvd_attestation_shares[att.data.slot][k] <= dv'.att_network.allMessagesSent;   
                assert att_shares <= dv'.att_network.allMessagesSent;   

                assert inv_attestation_is_created_with_shares_from_quorum_body(dv', att);
            }
        }
        assert inv_attestation_is_created_with_shares_from_quorum(dv');            
    }  

    lemma lem_inv_attestation_is_created_with_shares_from_quorum_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_only_dv_construct_signed_attestation_signature(dv)
    requires invNetwork(dv)
    requires inv_rcvd_attestation_shares_is_in_all_messages_sent(dv)
    requires inv_attestation_is_created_with_shares_from_quorum(dv)
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_attestation_is_created_with_shares_from_quorum(dv)
    ensures  inv_attestation_is_created_with_shares_from_quorum(dv')
    {        
        lem_inv_only_dv_construct_signed_attestation_signature_dv_next(dv, event, dv');
        assert inv_only_dv_construct_signed_attestation_signature(dv');

        lem_inv_unchanged_dvc_rs_pubkey_dv_next(dv, event, dv');
        assert ( forall hn: BLSPubkey | is_honest_node(dv, hn) ::
                        && hn == dv.honest_nodes_states[hn].rs.pubkey
                        && hn == dv'.honest_nodes_states[hn].rs.pubkey
        );

        lem_inv_rcvd_attestation_shares_is_in_all_messages_sent(dv, event, dv');

        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) =>     
                        lem_inv_outputs_attestations_submited_is_created_with_shares_from_quorum_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        if f_att_consensus_decided.requires(dvc, id, decided_attestation_data)
                        {
                            lem_inv_outputs_attestations_submited_is_created_with_shares_from_quorum_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');      
                        }                 
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_outputs_attestations_submited_is_created_with_shares_from_quorum_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_outputs_attestations_submited_is_created_with_shares_from_quorum_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendAttestationShares =>                         
                        
                    case NoEvent => 
                        
                }

                lem_inv_attestation_is_created_with_shares_from_quorum_dv_next_HonestNodeTakingStep(
                    dv,
                    event,
                    dv',
                    node, 
                    nodeEvent, 
                    nodeOutputs
                );

            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                lem_inv_attestation_is_created_with_shares_from_quorum_dv_next_AdeversaryTakingStep(
                    dv,
                    event,
                    dv'
                );
        }  
    }  

}