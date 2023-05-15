include "invs_fnc_1.dfy"

include "../../../../common/commons.dfy"

include "../../common/dvc_block_proposer_instrumented.dfy"
include "../../../bn_axioms.dfy"
include "../../../rs_axioms.dfy"

include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_block_proposer.dfy"

include "../inv.dfy"

include "../../common/common_proofs.dfy"
include "../../../common/quorum_lemmas.dfy"
include "invs_dv_next_1.dfy"


module Invs_DV_Next_2
{
    import opened Types
    
    import opened Common_Functions
    import opened Set_Seq_Helper
    import opened Signing_Methods
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Block_Proposer_Spec_Instr
    import opened Consensus_Engine_Instr
    import opened BN_Axioms
    import opened RS_Axioms
    import opened Block_Inv_With_Empty_Initial_Block_Slashing_DB
    import opened DV_Block_Proposer_Spec    
    import opened Fnc_Invs_1
    import opened Common_Proofs_For_Block_Proposer
    import opened Invs_DV_Next_1
    import opened Quorum_Lemmas
    import opened DV_Block_Proposer_Assumptions



    lemma lem_inv_all_in_transit_messages_were_sent_body_network_spec_next<M>(
        e: Network<M>,
        e': Network<M>,
        n: BLSPubkey,
        messagesToBeSent: set<MessaageWithRecipient<M>>,
        messagesReceived: set<M>
    )
    requires NetworkSpec.Next(e, e', n, messagesToBeSent, messagesReceived)
    requires inv_all_in_transit_messages_were_sent_body(e)
    ensures inv_all_in_transit_messages_were_sent_body(e')
    {
    
    }

    lemma lem_inv_all_in_transit_messages_were_sent_dv_next(
        dv: Block_DVState,
        event: DVBlockEvent,
        dv': Block_DVState
    )
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')
    requires inv_all_in_transit_messages_were_sent(dv)
    ensures inv_all_in_transit_messages_were_sent(dv')
    {
        var n: BLSPubkey,
            messagesToBeSent: set<MessaageWithRecipient<SignedBeaconBlock>>,
            messagesReceived: set<SignedBeaconBlock>
            :|
            NetworkSpec.Next<SignedBeaconBlock>(
                dv.block_share_network,
                dv'.block_share_network,
                n,
                messagesToBeSent,
                messagesReceived);

        lem_inv_all_in_transit_messages_were_sent_body_network_spec_next<SignedBeaconBlock>(
                dv.block_share_network,
                dv'.block_share_network,
                n,
                messagesToBeSent,
                messagesReceived);
    }

    lemma  lem_NextConsensus_monotonic_set_of_validity_functions<D(!new, 0)>(
        s: ConsensusInstance,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,
        s': ConsensusInstance,
        output: Optional<OutCommand>
    )
    requires ConsensusSpec.Next(
                        s,
                        honest_nodes_validity_predicates,
                        s',
                        output
                    );
    ensures s.honest_nodes_validity_functions.Keys <= s'.honest_nodes_validity_functions.Keys;
    {
    }

    lemma  lem_NextConsensus_monotonic_set_of_validity_functions_2<D(!new, 0)>(
        s: ConsensusInstance,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,
        s': ConsensusInstance,
        output: Optional<OutCommand>,
        n: BLSPubkey
    )
    requires ConsensusSpec.Next(
                        s,
                        honest_nodes_validity_predicates,
                        s',
                        output
                    );
    requires n in s.honest_nodes_validity_functions.Keys
    ensures s.honest_nodes_validity_functions[n] <= s'.honest_nodes_validity_functions[n];
    {
    }

    // TODO: Split this lemma into smaller pieces
    lemma lem_inv_decided_values_of_consensus_instances_are_decided_by_a_quorum_HonestNodeTakingStep(
        s: Block_DVState,
        event: DVBlockEvent,
        cid: Slot,
        s': Block_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires event.HonestNodeTakingStep?
    requires cid in s'.consensus_instances_on_beacon_block.Keys
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires inv_only_dv_construct_complete_signed_block(s)
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)
    requires s.consensus_instances_on_beacon_block[cid].decided_value.isPresent()
    ensures is_a_valid_decided_value(s'.consensus_instances_on_beacon_block[cid]);
    {
        assert s.block_share_network.allMessagesSent <= s'.block_share_network.allMessagesSent;
        match event
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];

                var s_w_honest_node_states_updated :=
                    if nodeEvent.ImportedNewBlock? then
                        s.(
                            honest_nodes_states := s.honest_nodes_states[node := f_add_block_to_bn(s.honest_nodes_states[node], nodeEvent.block)]
                        )
                    else
                        s
                    ;

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
                            && cid in s_w_honest_node_states_updated.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances.Keys
                        ::
                            s_w_honest_node_states_updated.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances[cid].validityPredicate
                    ;

                var s_consensus := s_w_honest_node_states_updated.consensus_instances_on_beacon_block[cid];
                var s'_consensus := s'.consensus_instances_on_beacon_block[cid];

                assert  ConsensusSpec.Next(
                            s_consensus,
                            validityPredicates,
                            s'_consensus,
                            output
                        );

                assert isConditionForSafetyTrue(s_consensus);
                assert && s'_consensus.decided_value.isPresent()
                       && s_consensus.decided_value.safe_get() == s'_consensus.decided_value.safe_get()
                       ;

                var h_nodes :| is_a_valid_decided_value_according_to_set_of_nodes(s_consensus, h_nodes);

                assert  s_consensus.honest_nodes_validity_functions.Keys <= s'_consensus.honest_nodes_validity_functions.Keys;
                assert  && var byz := s'.all_nodes - s'_consensus.honest_nodes_status.Keys;
                        && |h_nodes| >= quorum(|s.all_nodes|) - |byz|;

                lem_NextConsensus_monotonic_set_of_validity_functions(
                    s_consensus,
                    validityPredicates,
                    s'_consensus,
                    output
                );

                forall n | n in h_nodes
                ensures exists vp: BeaconBlock -> bool :: vp in s'_consensus.honest_nodes_validity_functions[n] && vp(s'_consensus.decided_value.safe_get());
                {
                    assert is_a_valid_decided_value(s_consensus);
                    var vp: BeaconBlock -> bool :| vp in s_consensus.honest_nodes_validity_functions[n] && vp(s_consensus.decided_value.safe_get());
                    lem_NextConsensus_monotonic_set_of_validity_functions_2(
                        s_consensus,
                        validityPredicates,
                        s'_consensus,
                        output,
                        n
                    );
                    lem_member_of_subset_is_member_of_superset(
                            vp, 
                            s_consensus.honest_nodes_validity_functions[n], 
                            s'_consensus.honest_nodes_validity_functions[n]
                    );
                    assert vp in s'_consensus.honest_nodes_validity_functions[n];
                    assert vp(s'_consensus.decided_value.safe_get());
                    assert exists vp: BeaconBlock -> bool :: vp in s'_consensus.honest_nodes_validity_functions[n] && vp(s'_consensus.decided_value.safe_get());
                }

                assert is_a_valid_decided_value_according_to_set_of_nodes(s'_consensus, h_nodes);
                assert is_a_valid_decided_value(s'_consensus);
        }
    }

    lemma lem_inv_decided_values_of_consensus_instances_are_decided_by_a_quorum_dv_next(
        s: Block_DVState,
        event: DVBlockEvent,
        s': Block_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires inv_only_dv_construct_complete_signed_block(s)
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)
    ensures inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s')
    {
        assert s.block_share_network.allMessagesSent <= s'.block_share_network.allMessagesSent;
        match event
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];

                var s_w_honest_node_states_updated :=
                    if nodeEvent.ImportedNewBlock? then
                        s.(
                            honest_nodes_states := s.honest_nodes_states[node := f_add_block_to_bn(s.honest_nodes_states[node], nodeEvent.block)]
                        )
                    else
                        s
                    ;

                forall cid | && cid in s'.consensus_instances_on_beacon_block.Keys
                             && s'.consensus_instances_on_beacon_block[cid].decided_value.isPresent()
                ensures is_a_valid_decided_value(s'.consensus_instances_on_beacon_block[cid]);
                {
                    if s.consensus_instances_on_beacon_block[cid].decided_value.isPresent()
                    {
                        lem_inv_decided_values_of_consensus_instances_are_decided_by_a_quorum_HonestNodeTakingStep(s, event, cid, s');
                    }
                    else
                    {
                        assert is_a_valid_decided_value(s'.consensus_instances_on_beacon_block[cid]);
                    }
                }
                assert inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s');


            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                assert inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s');
        }
    }

    lemma lem_inv_all_in_transit_messages_were_sent_inv_in_transit_messages_are_in_allMessagesSent(dv: Block_DVState)
    requires inv_all_in_transit_messages_were_sent(dv)
    ensures inv_in_transit_messages_are_in_allMessagesSent(dv)
    {        
    }

    lemma lem_inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k_helper(
        s: Block_DVState,
        cid: Slot
    )
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_nodes_in_consensus_instances_are_in_dv(s)
    requires cid in s.consensus_instances_on_beacon_block.Keys
    requires s.consensus_instances_on_beacon_block[cid].decided_value.isPresent()
    ensures s.consensus_instances_on_beacon_block[cid].decided_value.safe_get().slot == cid
    {
        var s_consensus := s.consensus_instances_on_beacon_block[cid];
        assert is_a_valid_decided_value(s_consensus);

        var h_nodes_a :| is_a_valid_decided_value_according_to_set_of_nodes(s_consensus, h_nodes_a);

        var byz := s.all_nodes - s.honest_nodes_states.Keys;

        assert byz * h_nodes_a == {} by
        {
            assert s.honest_nodes_states.Keys * byz == {};
        }

        lemmaThereExistsAnHonestInQuorum2(s.all_nodes, byz, h_nodes_a);

        var h_n :| h_n in h_nodes_a;

        var vp: BeaconBlock -> bool :| vp in s_consensus.honest_nodes_validity_functions[h_n] && vp(s_consensus.decided_value.safe_get());

        var proposer_duty, block_slashing_db, complete_randao_reveal :|
            inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(
                cid, 
                proposer_duty, 
                block_slashing_db, 
                complete_randao_reveal,
                vp);

        assert s_consensus.decided_value.safe_get().slot == cid;
    }

    lemma lem_inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k2(
        s: Block_DVState
    )
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_nodes_in_consensus_instances_are_in_dv(s)    
    ensures inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s)
    {
        forall cid | && cid in s.consensus_instances_on_beacon_block.Keys
                     && s.consensus_instances_on_beacon_block[cid].decided_value.isPresent()
        {
           lem_inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k_helper(s, cid);
        }
    }

    

    lemma lem_inv_rcvd_block_shares_are_in_all_sent_messages_dv_next(
        dv: Block_DVState,
        event: DVBlockEvent,
        dv': Block_DVState
    )
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')
    requires inv_in_transit_messages_are_in_allMessagesSent(dv)
    requires inv_rcvd_block_shares_are_in_all_sent_messages(dv)
    ensures inv_rcvd_block_shares_are_in_all_sent_messages(dv')
    {
        assert dv.block_share_network.allMessagesSent <= dv'.block_share_network.allMessagesSent;
        match event
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>
                        lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_serve_proposer_duty(dv, dvc, proposer_duty, dvc');

                    case ReceiveRandaoShare(randao_share) =>
                        lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_listen_for_randao_shares(dv, dvc, randao_share, dvc');

                    case BlockConsensusDecided(id, decided_beacon_block) =>
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_block_consensus_decided(dv, dvc, id, decided_beacon_block, dvc');
                        }

                    case ReceiveSignedBeaconBlock(block_share) =>
                        assert multiset(addReceipientToMessages<SignedBeaconBlock>({block_share}, node)) <= dv.block_share_network.messagesInTransit;
                        assert MessaageWithRecipient(message := block_share, receipient := node) in dv.block_share_network.messagesInTransit;
                        assert block_share in dv.block_share_network.allMessagesSent;
                        lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_listen_for_block_signature_shares(dv, dvc, block_share, dvc');

                    case ImportedNewBlock(block) =>
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_listen_for_new_imported_blocks(dv, dvc, block, dvc');

                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>

                    case NoEvent =>

                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>

        }
    }

    lemma lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        s': DVCState,
        dv: Block_DVState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires s' == f_listen_for_block_signature_shares(process, block_share).state
    requires construct_complete_signed_block_assumptions(
                process.construct_complete_signed_block,
                process.dv_pubkey,
                dv.all_nodes
            )
    requires inv_all_honest_nodes_is_a_quorum(dv)
    requires block_share in dv.block_share_network.allMessagesSent
    requires inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process)
    ensures forall block | block in f_listen_for_block_signature_shares(process, block_share).outputs.submitted_data
                        ::
                        exists hn', block_share: SignedBeaconBlock
                            ::
                            inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(dv, hn', block_share, block);
    {
        var slot := block_share.block.slot;

        if is_slot_for_current_or_future_instances(process, slot)
        {
            var data := block_share.block;
            var rcvd_block_shares_db_at_slot := getOrDefault(process.rcvd_block_shares, slot, map[]);
            var process_with_new_block_share :=
                process.(
                    rcvd_block_shares :=
                        process.rcvd_block_shares[
                            slot :=
                                rcvd_block_shares_db_at_slot[
                                    data :=
                                        getOrDefault(rcvd_block_shares_db_at_slot, data, {}) +
                                        {block_share}
                                    ]
                        ]
                );

            if process.construct_complete_signed_block(process_with_new_block_share.rcvd_block_shares[slot][data]).isPresent()
            {
                var block_shares := process_with_new_block_share.rcvd_block_shares[slot][data];
                var complete_block := process.construct_complete_signed_block(block_shares).safe_get();
                assert  construct_complete_signed_block_assumptions_reverse_helper(
                                            process.construct_complete_signed_block,
                                            process.dv_pubkey,
                                            dv.all_nodes,
                                            block_shares,
                                            complete_block           
                                        );

                var signing_root := compute_block_signing_root(complete_block.block);
                var signers :=
                    set signer, block_share |
                        && block_share in block_shares
                        && signer in dv.all_nodes
                        && verify_bls_signature(signing_root, block_share.signature, signer)
                    ::
                        signer;
                assert signers <= dv.all_nodes;
                assert signed_beacon_block_signer_threshold(dv.all_nodes, block_shares, signing_root);

                lemmaThereExistsAnHonestInQuorum(dv.all_nodes, dv.all_nodes - dv.honest_nodes_states.Keys, signers);

                var h_s :| h_s in dv.honest_nodes_states.Keys && h_s in signers;
                var h_s_block:| h_s_block in block_shares && verify_bls_signature(signing_root, h_s_block.signature, h_s);
                assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(
                            dv,
                            h_s,
                            h_s_block,
                            complete_block
                        );

                assert f_listen_for_block_signature_shares(process, block_share).outputs.submitted_data == {complete_block};

                assert forall a | a in f_listen_for_block_signature_shares(process, block_share).outputs.submitted_data ::
                            exists hn', block_share: SignedBeaconBlock :: inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(dv, hn', block_share, a);
            }
        }
    }

    lemma lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_when_no_new_blocks_are_added(
        s: Block_DVState,
        event: DVBlockEvent,
        s': Block_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s)
    requires s'.all_blocks_created == s.all_blocks_created
    ensures inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s');
    {
        forall block | block in s'.all_blocks_created
        ensures exists hn, block_share: SignedBeaconBlock :: inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s', hn, block_share, block);
        {
            var hn, block_share: SignedBeaconBlock :| inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s, hn, block_share, block);

            assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s', hn, block_share, block);
        }
    }

    lemma lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_dv_next_ReceiveSignedBeaconBlock(
        s: Block_DVState,
        event: DVBlockEvent,
        s': Block_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires event.HonestNodeTakingStep?
    requires event.event.ReceiveSignedBeaconBlock?
    requires inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s)
    requires construct_complete_signed_block_assumptions(
                s.construct_complete_signed_block,
                s.dv_pubkey,
                s.all_nodes
            )
    requires inv_only_dv_construct_complete_signed_block(s)
    requires inv_in_transit_messages_are_in_allMessagesSent(s)
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_rcvd_block_shares_are_in_all_sent_messages(s)
    ensures inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s')
    {
        assert s.block_share_network.allMessagesSent <= s'.block_share_network.allMessagesSent;
        match event
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ReceiveSignedBeaconBlock(block_share) =>
                        assert multiset(addReceipientToMessages<SignedBeaconBlock>({block_share}, node)) <= s.block_share_network.messagesInTransit;
                        assert MessaageWithRecipient(message := block_share, receipient := node) in s.block_share_network.messagesInTransit;

                        var stateAndOutput := f_listen_for_block_signature_shares(s_node, block_share);
                        assert block_share in s.block_share_network.allMessagesSent;
                        assert s'.all_blocks_created == s.all_blocks_created + stateAndOutput.outputs.submitted_data;
                        
                        lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_f_listen_for_block_signature_shares(
                            s_node,
                            block_share,
                            s'_node,
                            s
                        );

                        forall a |  && a in s'.all_blocks_created
                        ensures exists hn', block_share: SignedBeaconBlock :: inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s', hn', block_share, a);
                        {
                            if a in s.all_blocks_created
                            {
                                var hn', block_share: SignedBeaconBlock :| inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s, hn', block_share, a);
                                assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s', hn', block_share, a);
                            }
                            else
                            {
                                assert a in stateAndOutput.outputs.submitted_data;
                                var hn', block_share: SignedBeaconBlock :| inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s, hn', block_share, a);
                                assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s', hn', block_share, a);
                            }
                        }

                        assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s');
                }
        }
    }

    lemma lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_dv_next_AdversaryTakingStep(
        s: Block_DVState,
        event: DVBlockEvent,
        s': Block_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires event.AdversaryTakingStep?
    requires inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s)             
    requires construct_complete_signed_block_assumptions(
        s.construct_complete_signed_block,
        s.dv_pubkey,
        s.all_nodes
    )
    requires inv_only_dv_construct_complete_signed_block(s)
    requires inv_in_transit_messages_are_in_allMessagesSent(s)
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_rcvd_block_shares_are_in_all_sent_messages(s)
    ensures inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s')
    {
        assert s.block_share_network.allMessagesSent <= s'.block_share_network.allMessagesSent;
        match event
        {
            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                forall submitted_block |  submitted_block in s'.all_blocks_created
                ensures exists hn', block_share: SignedBeaconBlock :: inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s', hn', block_share, submitted_block);
                {
                    if submitted_block in s.all_blocks_created
                    {
                        var hn', block_share: SignedBeaconBlock :| inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s, hn', block_share, submitted_block);
                        assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s', hn', block_share, submitted_block);
                    }
                    else
                    {
                        assert submitted_block in s'.all_blocks_created - s.all_blocks_created;

                        var block_shares: set<SignedBeaconBlock> :| 
                            && block_shares <= s'.block_share_network.allMessagesSent
                            && s.construct_complete_signed_block(block_shares).isPresent()
                            && s.construct_complete_signed_block(block_shares).safe_get() == submitted_block
                            ;
                        var signing_root := compute_block_signing_root(submitted_block.block);
                        var signers :=
                            set signer, block_share |
                                && block_share in block_shares
                                && signer in s.all_nodes
                                && verify_bls_signature(signing_root, block_share.signature, signer)
                            ::
                                signer
                            ;
                        assert signers <= s.all_nodes;

                        lemmaThereExistsAnHonestInQuorum(s.all_nodes, s.all_nodes - s.honest_nodes_states.Keys, signers);

                        var h_s :| h_s in s.honest_nodes_states.Keys && h_s in signers;
                        var h_s_block_share :| h_s_block_share in block_shares && verify_bls_signature(signing_root, h_s_block_share.signature, h_s);

                        assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(
                                    s,
                                    h_s,
                                    h_s_block_share,
                                    submitted_block
                                );

                        assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(
                            s',
                            h_s,
                            h_s_block_share,
                            submitted_block
                        );
                    }
                }
                assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s');
        }
    }

    lemma lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_dv_next(
        s: Block_DVState,
        event: DVBlockEvent,
        s': Block_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s)
    requires construct_complete_signed_block_assumptions(
        s.construct_complete_signed_block,
        s.dv_pubkey,
        s.all_nodes
    )
    requires inv_only_dv_construct_complete_signed_block(s)
    requires inv_in_transit_messages_are_in_allMessagesSent(s)
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_rcvd_block_shares_are_in_all_sent_messages(s)
    ensures inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s')
    {
        assert s.block_share_network.allMessagesSent <= s'.block_share_network.allMessagesSent;
        match event
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>
                        lem_f_serve_proposer_duty_unchanged_vars(s_node, proposer_duty, s'_node);
                        lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_when_no_new_blocks_are_added(s, event, s');
                        assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s');

                    case ReceiveRandaoShare(randao_share) =>
                        lem_f_listen_for_randao_shares_unchanged_vars(s_node, randao_share, s'_node);
                        lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_when_no_new_blocks_are_added(s, event, s');
                        assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s');

                    case BlockConsensusDecided(id, decided_beacon_block) =>
                        lem_f_block_consensus_decided_unchanged_dvc_vars(s.honest_nodes_states[node], id, decided_beacon_block, s'.honest_nodes_states[node]);
                        lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_when_no_new_blocks_are_added(s, event, s');
                        assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s');

                    case ReceiveSignedBeaconBlock(block_share) =>
                        lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_dv_next_ReceiveSignedBeaconBlock(
                            s,
                            event,
                            s'
                        );

                    case ImportedNewBlock(block) =>
                        var s_node := f_add_block_to_bn(s_node, nodeEvent.block);
                        lem_f_listen_for_new_imported_blocks_unchanged_dvc_vars(s_node, block, s'_node);
                        lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_when_no_new_blocks_are_added(s, event, s');
                        assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s');

                    case ResendBlockShare =>
                        assert s'.all_blocks_created == s.all_blocks_created;
                        lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_when_no_new_blocks_are_added(s, event, s');
                        assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s');

                    case ResendRandaoRevealSignatureShare => 
                        assert s'.all_blocks_created == s.all_blocks_created;
                        lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_when_no_new_blocks_are_added(s, event, s');
                        assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s');

                    case NoEvent =>
                        assert s'.all_blocks_created == s.all_blocks_created;
                        lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_when_no_new_blocks_are_added(s, event, s');
                        assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s');
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_dv_next_AdversaryTakingStep(
                    s,
                    event,
                    s'
                );
        }
    }
    
    lemma lem_getMessagesFromEmptySetOfMessagesWithRecipient_is_empty_set<M>(mswr: set<MessaageWithRecipient<M>>)
    requires mswr == {}
    ensures getMessagesFromMessagesWithRecipient(mswr) == {}
    { }

    
}