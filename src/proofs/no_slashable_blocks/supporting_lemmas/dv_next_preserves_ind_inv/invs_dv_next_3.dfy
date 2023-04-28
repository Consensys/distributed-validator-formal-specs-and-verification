include "invs_fnc_1.dfy"
include "invs_fnc_2.dfy"

include "../../../../common/commons.dfy"

include "../../common/dvc_block_proposer_instrumented.dfy"
include "../../common/block_dvc_spec_axioms.dfy"

include "../../../../specs/consensus/block_consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_block_proposer.dfy"
include "../inv.dfy"

include "../../common/common_proofs.dfy"
include "../../common/block_dvc_spec_axioms.dfy"

include "../inv.dfy"
include "../../../common/helper_sets_lemmas.dfy"
include "../../../common/helper_pred_fcn.dfy"
include "../../common/common_proofs.dfy"

include "invs_dv_next_1.dfy"
include "invs_dv_next_2.dfy"

module Invs_DV_Next_3
{
    import opened Types
    
    import opened CommonFunctions
    import opened Block_Consensus_Spec
    import opened NetworkSpec
    import opened DVC_Block_Proposer_Spec_Instr
    import opened DVC_Block_Proposer_Spec_Axioms
    import opened Block_Inv_With_Empty_Initial_Block_Slashing_DB
    import opened DV_Block_Proposer_Spec    
    import opened Fnc_Invs_1
    import opened Fnc_Invs_2
    import opened Helper_Sets_Lemmas
    import opened Common_Proofs_For_Block_Proposer
    import opened Invs_DV_Next_1
    import opened Invs_DV_Next_2

    lemma f_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_get_s_w_honest_node_states_updated(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Types.BlockEvent
    ) returns (s_w_honest_node_states_updated: DVState)
    requires node in s.honest_nodes_states.Keys
    ensures s_w_honest_node_states_updated == add_block_to_bn_with_event(s, node, nodeEvent)
    ensures s_w_honest_node_states_updated == s.(honest_nodes_states := s_w_honest_node_states_updated.honest_nodes_states)
    ensures s_w_honest_node_states_updated.honest_nodes_states == s.honest_nodes_states[node := s_w_honest_node_states_updated.honest_nodes_states[node]]
    ensures s_w_honest_node_states_updated.honest_nodes_states[node] == s.honest_nodes_states[node].(bn := s_w_honest_node_states_updated.honest_nodes_states[node].bn)
    ensures s_w_honest_node_states_updated.consensus_instances_on_beacon_block.Keys == s.consensus_instances_on_beacon_block.Keys
    {
        s_w_honest_node_states_updated :=
        if nodeEvent.ImportedNewBlock? then
            s.(
                honest_nodes_states := s.honest_nodes_states[node := f_add_block_to_bn(s.honest_nodes_states[node], nodeEvent.block)]
            )
        else
            s           
        ;         
    }

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_get_s_w_honest_node_states_updated_2(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Types.BlockEvent,
        node': BLSPubkey,
        s_w_honest_node_states_updated: DVState
    )
    requires node in s.honest_nodes_states.Keys
    requires node' in s.honest_nodes_states.Keys
    requires s_w_honest_node_states_updated == add_block_to_bn_with_event(s, node, nodeEvent)
    ensures s_w_honest_node_states_updated.honest_nodes_states[node'].block_consensus_engine_state == s.honest_nodes_states[node'].block_consensus_engine_state
    {
    }

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_helper(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState,
        cid: Slot,
        hn: BLSPubkey,
        vp: BeaconBlock -> bool
    ) returns (proposer_duty: ProposerDuty, block_slashing_db: set<SlashingDBBlock>, randao_reveal: BLSSignature)
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires event.HonestNodeTakingStep?
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_nodes_in_consensus_instances_are_in_dv(s)
    requires inv_only_dv_construct_complete_signed_block(s)
    requires && hn in s'.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions.Keys
             && vp in s'.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions[hn]    
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(
                cid, 
                proposer_duty, 
                block_slashing_db, 
                randao_reveal, 
                vp);
    {
        assert s.block_share_network.allMessagesSent <= s'.block_share_network.allMessagesSent;
        match event
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];

                var s_w_honest_node_states_updated :=
                    f_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_get_s_w_honest_node_states_updated(s, node, nodeEvent);

                assert s_w_honest_node_states_updated.consensus_instances_on_beacon_block == s.consensus_instances_on_beacon_block;


                var output :=
                    if nodeEvent.BlockConsensusDecided? && nodeEvent.id == cid then
                        Some(Decided(node, nodeEvent.decided_beacon_block))
                    else
                        None
                    ;

                var validityPredicates :=
                    map n |
                            && n in s_w_honest_node_states_updated.honest_nodes_states.Keys
                            && cid in s_w_honest_node_states_updated.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys
                        ::
                            s_w_honest_node_states_updated.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid].validityPredicate
                    ;

                var s_consensus := s_w_honest_node_states_updated.consensus_instances_on_beacon_block[cid];
                var s'_consensus := s'.consensus_instances_on_beacon_block[cid];

                assert  Block_Consensus_Spec.Next(
                            s_consensus,
                            validityPredicates,
                            s'_consensus,
                            output
                        );

                if  && hn in s_consensus.honest_nodes_validity_functions.Keys  
                    && vp in s_consensus.honest_nodes_validity_functions[hn]
                {
                    assert vp in s'_consensus.honest_nodes_validity_functions[hn];

                    proposer_duty, block_slashing_db, randao_reveal :| inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(cid, proposer_duty, block_slashing_db, randao_reveal, vp);
                }
                else
                {
                    assert vp in validityPredicates.Values;

                    var vpn :| vpn in validityPredicates.Keys && validityPredicates[vpn] == vp;
                    assert validityPredicates[vpn] == s_w_honest_node_states_updated.honest_nodes_states[vpn].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid].validityPredicate;
                    assert vpn in s.honest_nodes_states.Keys;
                    assert cid in s_w_honest_node_states_updated.honest_nodes_states[vpn].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys;

                    lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_get_s_w_honest_node_states_updated_2(s, node, nodeEvent, vpn, s_w_honest_node_states_updated);

                    assert s_w_honest_node_states_updated.honest_nodes_states[vpn].block_consensus_engine_state == s.honest_nodes_states[vpn].block_consensus_engine_state;
                    assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc(s, vpn, cid);

                    proposer_duty, block_slashing_db, randao_reveal :| inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(cid, proposer_duty, block_slashing_db, randao_reveal, vp);
                }

                assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(cid, proposer_duty, block_slashing_db, randao_reveal, vp);
        }

    }

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_dv_next(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_nodes_in_consensus_instances_are_in_dv(s)
    requires inv_only_dv_construct_complete_signed_block(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s')
    {
        match event
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                forall hn, cid: Slot, vp |
                    && hn in s'.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions.Keys
                    && vp in s'.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions[hn]
                ensures exists proposer_duty, block_slashing_db, randao_reveal :: inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(cid, proposer_duty, block_slashing_db, randao_reveal, vp)
                {
                    var proposer_duty: ProposerDuty, block_slashing_db, randao_reveal := lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_helper(s, event, s', cid, hn, vp);
                }
                assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s');

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s');
        }
    }
    
    

    lemma lem_inv_blocks_of_in_transit_block_shares_are_decided_values_when_no_new_block_share_is_added_helper<M>(
        allMessagesSent': set<M>,
        allMessagesSent: set<M>,
        messagesToBeSent: set<MessaageWithRecipient<M>>
    )
    requires allMessagesSent' == allMessagesSent +
                                getMessagesFromMessagesWithRecipient(messagesToBeSent);
    requires messagesToBeSent == {}
    ensures allMessagesSent' == allMessagesSent
    { }

    lemma lem_inv_blocks_of_in_transit_block_shares_are_decided_values_when_no_new_block_share_is_added(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires inv_blocks_of_in_transit_block_shares_are_decided_values(s)
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires s'.block_share_network.allMessagesSent ==
                    s.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient({});
    ensures  inv_blocks_of_in_transit_block_shares_are_decided_values(s');
    {
        forall cid | cid in s.consensus_instances_on_beacon_block.Keys
        ensures && var s_consensus := s.consensus_instances_on_beacon_block[cid];
                && var s'_consensus := s'.consensus_instances_on_beacon_block[cid];
                && s_consensus.decided_value.isPresent() ==>
                        ( && s'_consensus.decided_value.isPresent()
                          && s_consensus.decided_value.safe_get() == s'_consensus.decided_value.safe_get()
                        )
            ;
        {
            var s_consensus := s.consensus_instances_on_beacon_block[cid];
            var s'_consensus := s'.consensus_instances_on_beacon_block[cid];

            assert isConditionForSafetyTrue(s_consensus);
            assert s_consensus.decided_value.isPresent() ==>
                && s'_consensus.decided_value.isPresent()
                && s_consensus.decided_value.safe_get() == s'_consensus.decided_value.safe_get()
            ;
        }

        assert forall cid | cid in s.consensus_instances_on_beacon_block.Keys ::
                    && var s_consensus := s.consensus_instances_on_beacon_block[cid];
                    && var s'_consensus := s'.consensus_instances_on_beacon_block[cid];
                    && s_consensus.decided_value.isPresent() ==>
                            ( && s'_consensus.decided_value.isPresent()
                            && s_consensus.decided_value.safe_get() == s'_consensus.decided_value.safe_get()
                            )
        ;

        var emptySet: set<MessaageWithRecipient<SignedBeaconBlock>> := {};
        calc {
            s'.block_share_network.allMessagesSent;
            ==
            s.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient(emptySet);
            ==
            {lem_getMessagesFromEmptySetOfMessagesWithRecipient_is_empty_set(emptySet);}
            s.block_share_network.allMessagesSent;
        }

        assert s'.block_share_network.allMessagesSent == s.block_share_network.allMessagesSent;

        forall hn, block_share |
                && hn in s'.honest_nodes_states.Keys
                && block_share in s'.block_share_network.allMessagesSent
                && var block_signing_root := compute_block_signing_root(block_share.block);
                && verify_bls_signature(block_signing_root, block_share.signature, hn)
        ensures inv_blocks_of_in_transit_block_shares_are_decided_values_body(s', block_share);
        {
            assert block_share in s.block_share_network.allMessagesSent;
            assert inv_blocks_of_in_transit_block_shares_are_decided_values_body(s, block_share);
            assert inv_blocks_of_in_transit_block_shares_are_decided_values_body(s', block_share);
        }

        assert inv_blocks_of_in_transit_block_shares_are_decided_values(s');
    }

     lemma lem_consensus_decision_is_unchanged<D(!new, 0)>(
        s: BlockConsensusInstance,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,
        s': BlockConsensusInstance,
        output: Optional<OutCommand>
    )
    requires Block_Consensus_Spec.Next(s, honest_nodes_validity_predicates, s', output)
    requires isConditionForSafetyTrue(s)
    requires s.decided_value.isPresent()
    ensures s'.decided_value.isPresent()
    ensures s.decided_value.safe_get() == s'.decided_value.safe_get()
    { }

    predicate is_correct_block_share(
        s: DVState,
        hn: BLSPubkey,
        block_share: SignedBeaconBlock
    )
    {
        && hn in s.honest_nodes_states.Keys 
        && block_share in s.block_share_network.allMessagesSent
        && var block_signing_root := compute_block_signing_root(block_share.block);
        && verify_bls_signature(block_signing_root, block_share.signature, hn)   
    }

    lemma lem_inv_blocks_of_in_transit_block_shares_are_decided_values_BlockConsensusDecided_block_of_inputs_is_decision_of_consensus_instance(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState,
        hn: BLSPubkey,
        block_share: SignedBeaconBlock
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires event.HonestNodeTakingStep?
    requires event.event.BlockConsensusDecided?
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires is_correct_block_share(s, hn, block_share)
    requires inv_blocks_of_in_transit_block_shares_are_decided_values(s)
    requires block_share in s.block_share_network.allMessagesSent
    ensures && s'.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.isPresent()
            && s'.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.safe_get() == block_share.block
    {
        match event
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case BlockConsensusDecided(id: Slot, decided_beacon_block) =>
                        assert inv_blocks_of_in_transit_block_shares_are_decided_values_body(s, block_share);
                        assert s.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.isPresent();
                        assert s.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.safe_get() == block_share.block;

                        var s_w_honest_node_states_updated := f_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_get_s_w_honest_node_states_updated(s, node, nodeEvent);
                        var cid := block_share.block.slot;

                        assert s_w_honest_node_states_updated.consensus_instances_on_beacon_block == s.consensus_instances_on_beacon_block;

                        var output :=
                            if nodeEvent.BlockConsensusDecided? && nodeEvent.id == cid 
                            then
                                Some(Decided(node, nodeEvent.decided_beacon_block))
                            else
                                None
                            ;

                        var validityPredicates :=
                            map n |
                                    && n in s_w_honest_node_states_updated.honest_nodes_states.Keys
                                    && cid in s_w_honest_node_states_updated.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys
                                ::
                                    s_w_honest_node_states_updated.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid].validityPredicate
                            ;

                        var s_consensus := s_w_honest_node_states_updated.consensus_instances_on_beacon_block[cid];
                        var s'_consensus := s'.consensus_instances_on_beacon_block[cid];

                        assert  Block_Consensus_Spec.Next(
                                    s_consensus,
                                    validityPredicates,
                                    s'_consensus,
                                    output
                                );

                        lem_consensus_decision_is_unchanged(
                            s_consensus,
                            validityPredicates,
                            s'_consensus,
                            output
                        );
                }
        }
    }

    lemma lem_inv_blocks_of_in_transit_block_shares_are_decided_values_BlockConsensusDecided_with_decided_data_for_current_slot(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState,
        node: BLSPubkey,
        nodeEvent: Types.BlockEvent,
        nodeOutputs: Outputs,
        id: Slot,
        decided_beacon_block: BeaconBlock
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires event.HonestNodeTakingStep?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires nodeEvent.BlockConsensusDecided?
    requires nodeEvent == BlockConsensusDecided(id, decided_beacon_block)
    requires inv_blocks_of_in_transit_block_shares_are_decided_values(s)
    requires inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s)
    requires inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    requires && var process := s.honest_nodes_states[node];
             && process.current_proposer_duty.isPresent()
             && process.current_proposer_duty.safe_get().slot == decided_beacon_block.slot
             && id == decided_beacon_block.slot
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_nodes_in_consensus_instances_are_in_dv(s) 
    requires inv_only_dv_construct_complete_signing_functions(s)
    ensures inv_blocks_of_in_transit_block_shares_are_decided_values(s')
    {   
        assert inv_only_dv_construct_complete_signed_block(s);

        var process := s.honest_nodes_states[node];
        var process' := s'.honest_nodes_states[node];

        var slot := decided_beacon_block.slot;
        var block_signing_root := compute_block_signing_root(decided_beacon_block);
        var fork_version := bn_get_fork_version(slot);
        var block_signature := rs_sign_block(decided_beacon_block, fork_version, block_signing_root, process.rs);
        var block_share := SignedBeaconBlock(decided_beacon_block, block_signature);
        
        var messagesToBeSent := f_block_consensus_decided(process, id, decided_beacon_block).outputs.sent_block_shares;

        assert  messagesToBeSent ==  multicast(block_share, process.peers);
        assert  s'.block_share_network.allMessagesSent ==
                s.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent);
        assert forall m | m in messagesToBeSent :: m.message == block_share;

        lemmaOnGetMessagesFromMessagesWithRecipientWhenAllMessagesAreTheSame(messagesToBeSent, block_share);
        assert getMessagesFromMessagesWithRecipient(messagesToBeSent) == {block_share};
        assert  s'.block_share_network.allMessagesSent ==
                s.block_share_network.allMessagesSent + { block_share };

        forall hn, block_share |
                && hn in s'.honest_nodes_states.Keys
                && block_share in s'.block_share_network.allMessagesSent
                && var block_signing_root := compute_block_signing_root(block_share.block);
                && verify_bls_signature(block_signing_root, block_share.signature, hn)
        ensures s'.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.isPresent();
        ensures s'.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.safe_get() == block_share.block;
        {
            if block_share in s.block_share_network.allMessagesSent
            {
                lem_inv_blocks_of_in_transit_block_shares_are_decided_values_BlockConsensusDecided_block_of_inputs_is_decision_of_consensus_instance(s, event, s', hn, block_share);
            }
            else
            {
                assert block_share == block_share;
                lemmaImaptotalElementInDomainIsInKeys(s.consensus_instances_on_beacon_block, id);
                assert id in s.consensus_instances_on_beacon_block.Keys ;
                 
                lem_inv_blocks_of_in_transit_block_shares_are_decided_values_BlockConsensusDecided_block_in_inputs_is_decided_value(s, event, s');
                assert s'.consensus_instances_on_beacon_block[id].decided_value.safe_get() == decided_beacon_block;
                assert s'.consensus_instances_on_beacon_block[id].decided_value.safe_get() == block_share.block;

                lem_inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k_dv_next(s, event, s');
            }
        }

        assert inv_blocks_of_in_transit_block_shares_are_decided_values(s');
    }

    lemma lem_inv_blocks_of_in_transit_block_shares_are_decided_values_dv_next_ServeProposerDuty(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires event.HonestNodeTakingStep?
    requires event.event.ServeProposerDuty?
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires inv_blocks_of_in_transit_block_shares_are_decided_values(s)
    ensures inv_blocks_of_in_transit_block_shares_are_decided_values(s')
    {
        match event
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>
                        var sentBlockShares := f_serve_proposer_duty(s_node, proposer_duty).outputs.sent_block_shares;

                        lem_f_serve_proposer_duty_unchanged_vars(s_node, proposer_duty, s'_node);
                        assert  sentBlockShares == {};
                        assert  s'.block_share_network.allMessagesSent ==
                                s.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient(sentBlockShares);
                        lem_inv_blocks_of_in_transit_block_shares_are_decided_values_when_no_new_block_share_is_added_helper(s'.block_share_network.allMessagesSent, s.block_share_network.allMessagesSent, sentBlockShares);
                        assert s'.block_share_network.allMessagesSent == s.block_share_network.allMessagesSent;
                        lem_inv_blocks_of_in_transit_block_shares_are_decided_values_when_no_new_block_share_is_added(s, event, s');
                }
        }
    }

    lemma lem_inv_blocks_of_in_transit_block_shares_are_decided_values_dv_next_ReceiveRandaoShare(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires event.HonestNodeTakingStep?
    requires event.event.ReceiveRandaoShare?
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires inv_blocks_of_in_transit_block_shares_are_decided_values(s)
    ensures inv_blocks_of_in_transit_block_shares_are_decided_values(s')
    {
        match event
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ReceiveRandaoShare(randao_share) =>
                        var sentBlockShares := f_listen_for_randao_shares(s_node, randao_share).outputs.sent_block_shares;

                        lem_f_listen_for_randao_shares_unchanged_vars(s_node, randao_share, s'_node);
                        assert  sentBlockShares == {};
                        assert  s'.block_share_network.allMessagesSent ==
                                s.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient(sentBlockShares);
                        lem_inv_blocks_of_in_transit_block_shares_are_decided_values_when_no_new_block_share_is_added_helper(s'.block_share_network.allMessagesSent, s.block_share_network.allMessagesSent, sentBlockShares);
                        assert s'.block_share_network.allMessagesSent == s.block_share_network.allMessagesSent;
                        lem_inv_blocks_of_in_transit_block_shares_are_decided_values_when_no_new_block_share_is_added(s, event, s');
                }
        }
    }

    lemma lem_inv_blocks_of_in_transit_block_shares_are_decided_values_BlockConsensusDecided_block_in_inputs_is_decided_value(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires event.HonestNodeTakingStep?
    requires event.event.BlockConsensusDecided?
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_nodes_in_consensus_instances_are_in_dv(s)
    ensures s'.consensus_instances_on_beacon_block[event.event.id].decided_value.safe_get() == event.event.decided_beacon_block;
    {
        match event
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case BlockConsensusDecided(id: Slot, decided_beacon_block) =>
                        var s_w_honest_node_states_updated := f_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_get_s_w_honest_node_states_updated(s, node, nodeEvent);
                        var cid := id;

                        assert s_w_honest_node_states_updated.consensus_instances_on_beacon_block == s.consensus_instances_on_beacon_block;

                        var output := Some(Decided(node, nodeEvent.decided_beacon_block));

                        var validityPredicates :=
                                map n |
                                        && n in s_w_honest_node_states_updated.honest_nodes_states.Keys
                                        && cid in s_w_honest_node_states_updated.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys
                                    ::
                                        s_w_honest_node_states_updated.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid].validityPredicate
                                ;

                        var s_consensus := s_w_honest_node_states_updated.consensus_instances_on_beacon_block[cid];
                        var s'_consensus := s'.consensus_instances_on_beacon_block[cid];

                        assert Block_Consensus_Spec.Next(
                                    s_consensus,
                                    validityPredicates,
                                    s'_consensus,
                                    output
                                );

                        assert s'.consensus_instances_on_beacon_block[id].decided_value.isPresent();
                        assert isConditionForSafetyTrue(s'_consensus);
                        assert s'_consensus.decided_value.safe_get() == decided_beacon_block;
                        assert s'.consensus_instances_on_beacon_block[id].decided_value.safe_get() == decided_beacon_block;
                }
        }
    }

    lemma lem_inv_blocks_of_in_transit_block_shares_are_decided_values_BlockConsensusDecided(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires event.HonestNodeTakingStep?
    requires event.event.BlockConsensusDecided?
    requires inv_blocks_of_in_transit_block_shares_are_decided_values(s)
    requires inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s)
    requires inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(s)
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_nodes_in_consensus_instances_are_in_dv(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires inv_only_dv_construct_complete_signing_functions(s)
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    ensures inv_blocks_of_in_transit_block_shares_are_decided_values(s')
    {
        match event
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var process := s.honest_nodes_states[node];
                var process' := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case BlockConsensusDecided(id: Slot, decided_beacon_block) =>
                        if  && process.current_proposer_duty.isPresent()
                            && process.current_proposer_duty.safe_get().slot == decided_beacon_block.slot
                            && id == decided_beacon_block.slot
                        {
                            lem_inv_blocks_of_in_transit_block_shares_are_decided_values_BlockConsensusDecided_with_decided_data_for_current_slot(
                                s,
                                event,
                                s',
                                node,
                                nodeEvent,
                                nodeOutputs,
                                id,
                                decided_beacon_block
                            );
                        }
                        else
                        {
                            var sentBlockShares := f_block_consensus_decided(process, id, decided_beacon_block).outputs.sent_block_shares;

                            assert  sentBlockShares == {};
                            assert  s'.block_share_network.allMessagesSent ==
                                    s.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient(sentBlockShares);
                            lem_inv_blocks_of_in_transit_block_shares_are_decided_values_when_no_new_block_share_is_added_helper(s'.block_share_network.allMessagesSent, s.block_share_network.allMessagesSent, sentBlockShares);
                            assert s'.block_share_network.allMessagesSent == s.block_share_network.allMessagesSent;
                            lem_inv_blocks_of_in_transit_block_shares_are_decided_values_when_no_new_block_share_is_added(s, event, s');
                        }
                }
        }
    }

    lemma lem_inv_blocks_of_in_transit_block_shares_are_decided_values_dv_next_ReceiveSignedBeaconBlock(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires event.HonestNodeTakingStep?
    requires event.event.ReceiveSignedBeaconBlock?
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires inv_blocks_of_in_transit_block_shares_are_decided_values(s)
    ensures inv_blocks_of_in_transit_block_shares_are_decided_values(s')
    {
        match event
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ReceiveSignedBeaconBlock(block_share) =>
                        var sentBlockShares := f_listen_for_block_signature_shares(s_node, block_share).outputs.sent_block_shares;

                        lem_f_listen_for_block_signature_shares_unchanged_vars(s_node, block_share, s'_node);
                        assert  sentBlockShares == {};
                        assert  s'.block_share_network.allMessagesSent ==
                                s.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient(sentBlockShares);
                        lem_inv_blocks_of_in_transit_block_shares_are_decided_values_when_no_new_block_share_is_added_helper(s'.block_share_network.allMessagesSent, s.block_share_network.allMessagesSent, sentBlockShares);
                        assert s'.block_share_network.allMessagesSent == s.block_share_network.allMessagesSent;
                        lem_inv_blocks_of_in_transit_block_shares_are_decided_values_when_no_new_block_share_is_added(s, event, s');
                }
        }
    }

    lemma lem_inv_blocks_of_in_transit_block_shares_are_decided_values_dv_next_ImportedNewBlock(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires event.HonestNodeTakingStep?
    requires event.event.ImportedNewBlock?
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires inv_blocks_of_in_transit_block_shares_are_decided_values(s)
    ensures inv_blocks_of_in_transit_block_shares_are_decided_values(s')
    {
        match event
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ImportedNewBlock(block) =>
                        var s_node := f_add_block_to_bn(s_node, nodeEvent.block);                        
                        var messagesToBeSent := f_listen_for_new_imported_blocks(s_node, block).outputs.sent_block_shares;
                        assert f_listen_for_new_imported_blocks.requires(s_node, block);
                        assert s'_node == f_listen_for_new_imported_blocks(s_node, block).state;                        

                        lem_f_listen_for_new_imported_blocks_unchanged_dvc_vars(s_node, block, s'_node);
                        assert messagesToBeSent == {};
                        assert  s'.block_share_network.allMessagesSent ==
                                s.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent);                        
                        
                        lem_inv_blocks_of_in_transit_block_shares_are_decided_values_when_no_new_block_share_is_added_helper(s'.block_share_network.allMessagesSent, s.block_share_network.allMessagesSent, messagesToBeSent);
                        assert s'.block_share_network.allMessagesSent == s.block_share_network.allMessagesSent;
                        
                        lem_inv_blocks_of_in_transit_block_shares_are_decided_values_when_no_new_block_share_is_added(s, event, s');
                }
        }
    }

    lemma lem_inv_blocks_of_in_transit_block_shares_are_decided_values_dv_next_ResendBlockShare(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires event.HonestNodeTakingStep?
    requires event.event.ResendBlockShare?
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires inv_blocks_of_in_transit_block_shares_are_decided_values(s)
    requires inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(s)
    ensures inv_blocks_of_in_transit_block_shares_are_decided_values(s')
    {
        match event
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ResendBlockShare =>
                        var messagesToBeSent := f_resend_block_share(s_node).outputs.sent_block_shares;

                            assert s'.block_share_network.allMessagesSent ==
                                        s.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent);

                            forall m | m in getMessagesFromMessagesWithRecipient(messagesToBeSent)
                            ensures m in s.block_share_network.allMessagesSent
                            {
                                assert m in s_node.block_shares_to_broadcast.Values;
                                assert m in s.block_share_network.allMessagesSent;
                            }

                            assert s'.block_share_network.allMessagesSent == s.block_share_network.allMessagesSent;
                            lem_inv_blocks_of_in_transit_block_shares_are_decided_values_when_no_new_block_share_is_added(s, event, s');
                }
        }
    }

    lemma lem_inv_blocks_of_in_transit_block_shares_are_decided_values_proposer_adversary(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires event.AdversaryTakingStep?
    requires inv_blocks_of_in_transit_block_shares_are_decided_values(s)
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires inv_only_dv_construct_complete_signed_block(s)
    ensures inv_blocks_of_in_transit_block_shares_are_decided_values(s')
    {
        var new_sent_block_shares := s'.block_share_network.allMessagesSent - s.block_share_network.allMessagesSent;

        forall hn, block_share |
                && hn in s'.honest_nodes_states.Keys
                && block_share in s'.block_share_network.allMessagesSent
                && var block_signing_root := compute_block_signing_root(block_share.block);
                && verify_bls_signature(block_signing_root, block_share.signature, hn)
        ensures s'.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.isPresent();
        ensures s'.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.safe_get() == block_share.block;
        {
            var block_signing_root := compute_block_signing_root(block_share.block);

            if block_share in s.block_share_network.allMessagesSent
            {
                assert s.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.isPresent();
                assert s.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.safe_get() == block_share.block;
            }
            else
            {
                forall signer | verify_bls_signature(block_signing_root, block_share.signature, signer)
                ensures signer in s.adversary.nodes;
                ensures signer !in  s.honest_nodes_states.Keys;
                {

                    assert signer in s.adversary.nodes;
                    lemmaEmptyIntersectionImpliesDisjointness(s.adversary.nodes, s.honest_nodes_states.Keys);
                    assert s.adversary.nodes !! s.honest_nodes_states.Keys;
                    assert signer !in  s.honest_nodes_states.Keys;
                }
                assert false;
            }
        }

        assert inv_blocks_of_in_transit_block_shares_are_decided_values(s');
    }


    lemma lem_inv_blocks_of_in_transit_block_shares_are_decided_values_dv_next(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_nodes_in_consensus_instances_are_in_dv(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires inv_only_dv_construct_complete_signing_functions(s)
    requires inv_blocks_of_in_transit_block_shares_are_decided_values(s)
    requires inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s)
    requires inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(s)
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    ensures inv_blocks_of_in_transit_block_shares_are_decided_values(s')
    {
        match event
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := s.honest_nodes_states[node];
                var dvc' := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_blocks_of_in_transit_block_shares_are_decided_values_dv_next_ServeProposerDuty(s, event, s');

                    case ReceiveRandaoShare(randao_share) =>        
                        lem_inv_blocks_of_in_transit_block_shares_are_decided_values_dv_next_ReceiveRandaoShare(s, event, s');  
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            lem_inv_blocks_of_in_transit_block_shares_are_decided_values_BlockConsensusDecided(s, event, s');        
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>             
                        lem_inv_blocks_of_in_transit_block_shares_are_decided_values_dv_next_ReceiveSignedBeaconBlock(s, event, s');           
   
                    case ImportedNewBlock(block) => 
                        lem_inv_blocks_of_in_transit_block_shares_are_decided_values_dv_next_ImportedNewBlock(s, event, s');           

                    case ResendRandaoRevealSignatureShare =>
                        lem_inv_blocks_of_in_transit_block_shares_are_decided_values_when_no_new_block_share_is_added(s, event, s');

                    case ResendBlockShare =>
                        lem_inv_blocks_of_in_transit_block_shares_are_decided_values_dv_next_ResendBlockShare(s, event, s');
                        
                    case NoEvent => 
                        assert s'.block_share_network == s.block_share_network;
                        lem_inv_blocks_of_in_transit_block_shares_are_decided_values_when_no_new_block_share_is_added(s, event, s');
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                lem_inv_blocks_of_in_transit_block_shares_are_decided_values_proposer_adversary(s, event, s');
        }
    }

    lemma lem_inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k_dv_next(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_nodes_in_consensus_instances_are_in_dv(s)    
    requires inv_only_dv_construct_complete_signing_functions(s)
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    ensures inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s')
    {
        lem_inv_all_honest_nodes_is_a_quorum_dv_next(s, event, s');
        lem_inv_nodes_in_consensus_instances_are_in_dv_dv_next(s, event, s');
        lem_inv_only_dv_construct_complete_signing_functions_dv_next(s, event, s');
        assert inv_only_dv_construct_complete_signed_block(s');
        lem_inv_decided_values_of_consensus_instances_are_decided_by_a_quorum_dv_next(s, event, s');
        lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_dv_next(s, event, s');
        lem_inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k2(s');
    }

    lemma lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties(dv)
    requires inv_current_proposer_duty_is_a_rcvd_duty(dv)
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist(dv)
    requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties(dv)  
    ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>   
                        assert inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(dvc);   
                        assert inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(dvc);                                           
                        lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_serve_proposer_duty(dvc, proposer_duty, dvc');
                        assert inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(dvc');

                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_listen_for_randao_shares(dvc, randao_share, dvc');    
                        assert inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(dvc');                        

                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');
                            assert inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(dvc');
                        }
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_listen_for_block_signature_shares(dvc, block_share, dvc');
                        assert inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := f_add_block_to_bn(dvc, block);
                        lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(dvc_mod);
                        lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(dvc');

                    case ResendBlockShare =>      

                    case ResendRandaoRevealSignatureShare =>                                                                

                    case NoEvent => 
                        
                }
                
            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    }

    lemma lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k(dv)
    requires inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate(dv)
    ensures inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_f_serve_proposer_duty(dvc, proposer_duty, dvc');
                    
                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_f_listen_for_randao_shares(dvc, randao_share, dvc');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_f_listen_for_block_signature_shares(dvc, block_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    } 

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k(dv)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body_f_serve_proposer_duty(dvc, proposer_duty, dvc');
                    
                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body_f_listen_for_randao_shares(dvc, randao_share, dvc');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body_f_listen_for_block_signature_shares(dvc, block_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    } 

    lemma lem_inv_block_slashing_db_hist_is_monotonic_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    ensures inv_block_slashing_db_hist_is_monotonic(dv, event, dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_block_slashing_db_hist_is_monotonic_body_f_serve_proposer_duty(dvc, proposer_duty, dvc');
                    
                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_block_slashing_db_hist_is_monotonic_body_f_listen_for_randao_shares(dvc, randao_share, dvc');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            lem_inv_block_slashing_db_hist_is_monotonic_body_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_block_slashing_db_hist_is_monotonic_body_f_listen_for_block_signature_shares(dvc, block_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_block_slashing_db_hist_is_monotonic_body_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    } 


    lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k(dv)
    requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db(dv)  
    ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>   
                        assert inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(dvc);   
                        assert inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(dvc);                                           
                        lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_serve_proposer_duty(dvc, proposer_duty, dvc');
                        assert inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(dvc');

                    case ReceiveRandaoShare(randao_share) =>        
                        lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_listen_for_randao_shares(dvc, randao_share, dvc');   
                        assert inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(dvc');                        

                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');
                        assert inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(dvc');
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_listen_for_block_signature_shares(dvc, block_share, dvc');
                        assert inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := f_add_block_to_bn(dvc, block);
                        lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(dvc_mod);
                        lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(dvc');

                    case ResendRandaoRevealSignatureShare =>
                        assert inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(dvc');
                    
                    case ResendBlockShare =>                                                                    
                        assert inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(dvc');  

                    case NoEvent => 
                        assert inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(dvc');
                        
                }
                
            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                assert inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db(dv');
                
        }   
    }

      

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv_dv_next(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_nodes_in_consensus_instances_are_in_dv(s)
    requires inv_only_dv_construct_complete_signed_block(s)
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k(s)
    requires inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate(s)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s')
    {
        match event
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := s.honest_nodes_states[node];
                var dvc' := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>
                        lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_serve_proposer_duty(dvc, proposer_duty, dvc');

                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_listen_for_randao_shares(dvc, randao_share, dvc');

                    case BlockConsensusDecided(id, decided_beacon_block) =>
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');      
                        }   

                    case ReceiveSignedBeaconBlock(block_share) =>
                        lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_listen_for_block_signature_shares(dvc, block_share, dvc');

                    case ImportedNewBlock(block) =>
                        var dvc_after_adding_new_block := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_add_block_to_bn(
                            dvc,
                            block,
                            dvc_after_adding_new_block
                        );
                        lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_listen_for_new_imported_blocks(
                            dvc_after_adding_new_block, 
                            block, 
                            dvc'
                        );                            

                    case ResendRandaoRevealSignatureShare =>
                        lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_resend_randao_share(dvc, dvc');

                    case ResendBlockShare =>
                        lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_resend_block_share(dvc, dvc');

                    case NoEvent =>
                        assert dvc == dvc';

                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s');
        }
    }
}   
        