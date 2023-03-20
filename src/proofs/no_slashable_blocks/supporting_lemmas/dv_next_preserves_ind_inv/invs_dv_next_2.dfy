include "invs_fnc_1.dfy"

include "../../../../common/block_proposer/block_types.dfy"
include "../../../../common/block_proposer/block_common_functions.dfy"
include "../../../../common/block_proposer/block_signing_functions.dfy"
include "../../common/dvc_block_proposer_instrumented.dfy"
include "../../../../specs/consensus/block_consensus.dfy"
include "../../../../specs/network/block_network.dfy"
include "../../../../specs/dv/dv_block_proposer.dfy"
include "../inv.dfy"

include "../../common/common_proofs.dfy"
include "../../common/block_dvc_spec_axioms.dfy"


include "../inv.dfy"
include "../../../common/helper_sets_lemmas.dfy"
include "../../../common/helper_pred_fcn.dfy"


include "invs_dv_next_1.dfy"


module Invs_DV_Next_2
{
    import opened Block_Types
    import opened Block_Signing_Functions
    import opened Block_Common_Functions
    import opened Block_Consensus_Spec
    import opened Block_Network_Spec
    import opened DVC_Block_Proposer_Spec_Instr
    import opened Block_Inv_With_Empty_Initial_Block_Slashing_DB
    import opened DV_Block_Proposer_Spec
    import opened Fnc_Invs_1
    import opened Helper_Sets_Lemmas
    import opened Invs_DV_Next_1




    // lemma lem_ServeProposerDuty2_helper(
    //     s: DVState,
    //     node: BLSPubkey,
    //     nodeEvent: Block_Types.Event,
    //     nodeOutputs: DVC_Block_Proposer_Spec_Instr.Outputs,
    //     s': DVState
    // )
    // requires NextHonestAfterAddingBlockToBn.requires(s, node, nodeEvent, nodeOutputs, s' );
    // requires NextHonestAfterAddingBlockToBn(s, node, nodeEvent, nodeOutputs, s' );
    // requires nodeEvent.ServeProposerDuty?
    // ensures s'.index_next_proposer_duty_to_be_served > 0
    // ensures && inv_the_latest_proposer_duty_was_sent_from_dv(s', s'.index_next_proposer_duty_to_be_served, nodeEvent.proposer_duty, node )
    //         && s.index_next_proposer_duty_to_be_served == s'.index_next_proposer_duty_to_be_served - 1;
    // {

    //     var s_node := s.honest_nodes_states[node];
    //     var s'_node := s'.honest_nodes_states[node];
    //     assert  NextHonestAfterAddingBlockToBn.requires(add_block_to_bn_with_event(s, node, nodeEvent), node, nodeEvent, nodeOutputs, s' );
    //     assert  NextHonestAfterAddingBlockToBn(add_block_to_bn_with_event(s, node, nodeEvent), node, nodeEvent, nodeOutputs, s' );

    //     match nodeEvent
    //     {
    //         case ServeProposerDuty(proposer_duty) =>
    //             assert s.sequence_proposer_duties_to_be_served == s'.sequence_proposer_duties_to_be_served;
    //             assert s.index_next_proposer_duty_to_be_served == s'.index_next_proposer_duty_to_be_served - 1;

    //             var an := s'.sequence_proposer_duties_to_be_served[s'.index_next_proposer_duty_to_be_served - 1];

    //             assert proposer_duty == an.proposer_duty;
    //             assert node == an.node;
    //     }
    // }

    // // TODO: Rename to lem_ServeProposerDuty
    // lemma lem_ServeProposerDuty(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires event.HonestNodeTakingStep?
    // requires event.event.ServeProposerDuty?
    // ensures s'.index_next_proposer_duty_to_be_served > 0
    // ensures && inv_the_latest_proposer_duty_was_sent_from_dv(s', s'.index_next_proposer_duty_to_be_served, event.event.proposer_duty, event.node )
    //         && s.index_next_proposer_duty_to_be_served == s'.index_next_proposer_duty_to_be_served - 1;
    // {
    //     assert s.block_share_network.allMessagesSent <= s'.block_share_network.allMessagesSent;
    //     match event
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             var s_node := s.honest_nodes_states[node];
    //             var s'_node := s'.honest_nodes_states[node];
    //             assert  NextHonestAfterAddingBlockToBn.requires(add_block_to_bn_with_event(s, node, nodeEvent), node, nodeEvent, nodeOutputs, s' );
    //             assert  NextHonestAfterAddingBlockToBn(add_block_to_bn_with_event(s, node, nodeEvent), node, nodeEvent, nodeOutputs, s' );
    //             lem_ServeProposerDuty2_helper(add_block_to_bn_with_event(s, node, nodeEvent), node, nodeEvent, nodeOutputs, s' );
    //     }
    // }

    // function recover_bls_signature(
    //     r: Root,
    //     signature: BLSSignature
    // ): BLSPubkey
    // requires exists pubkey :: verify_bls_signature(r, signature, pubkey)
    // {
    //     var pubkey :| verify_bls_signature(r, signature, pubkey);
    //     pubkey
    // }

    // lemma lem_recover_bls_signature()
    // ensures forall r, s1, s2 |
    //             && recover_bls_signature.requires(r, s1)
    //             && recover_bls_signature.requires(r, s2)
    //             && recover_bls_signature(r, s1) == recover_bls_signature(r, s2)
    //         ::
    //             s1 == s2
    // {
    //     lem_verify_bls_signature();
    // }

    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    // // TODO: The current proof for non-slashable proposers does not require the following lemma.
    // // However, we still keep them here as they might be useful in the future.
    // // lemma lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_f_listen_for_block_signature_shares(
    // //     process: DVCState,
    // //     block_share: SignedBeaconBlock,
    // //     s': DVCState,
    // //     dv: DVState
    // // )
    // // requires f_listen_for_block_signature_shares.requires(process, block_share)
    // // requires s' == f_listen_for_block_signature_shares(process, block_share).state
    // // requires construct_complete_signed_block_assumptions_helper(
    // //     process.construct_complete_signed_block,
    // //     process.dv_pubkey,
    // //     dv.all_nodes
    // // )
    // // requires inv_quorum_constraints(dv)
    // // requires block_share in dv.block_share_network.allMessagesSent
    // // requires inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process)
    // // requires ( forall a | a in process.bn.submitted_blocks :: exists hn', block_share: SignedBeaconBlock ::
    // //                 inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(dv, hn', block_share, a)
    // //          )
    // // ensures forall a | a in s'.bn.submitted_blocks :: exists hn', block_share: SignedBeaconBlock :: inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(dv, hn', block_share, a)
    // // {
    // //     var activate_proposer_consensus_intances := process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys;

    // //     if pred_listen_for_block_shares_checker(
    // //             process,
    // //             block_share)
    // //     {
    // //         var k := (block_share.block, block_share.aggregation_bits);
    // //         var process := f_add_new_block_share(
    // //                                 process,
    // //                                 block_share
    // //                             );


    // //         if process.construct_complete_signed_block(process.rcvd_block_shares[block_share.block.slot][k]).isPresent()
    // //         {
    // //             var aggregated_proposer :=
    // //                     Attestation(
    // //                         aggregation_bits := block_share.aggregation_bits,
    // //                         data := block_share.block,
    // //                         signature := process.construct_complete_signed_block(process.rcvd_block_shares[block_share.block.slot][k]).safe_get()
    // //                     );

    // //             var block_shares := process.rcvd_block_shares[block_share.block.slot][k];
    // //             assert construct_complete_signed_block_assumptions_reverse(
    // //                 process.construct_complete_signed_block,
    // //                 process.dv_pubkey,
    // //                 dv.all_nodes
    // //             );

    // //             assert process.construct_complete_signed_block(block_shares).isPresent();

    // //             assert construct_complete_signed_block_assumptions_reverse(
    // //                 process.construct_complete_signed_block,
    // //                 process.dv_pubkey,
    // //                 dv.all_nodes
    // //             );

    // //             var data: BeaconBlock :|
    // //                 construct_complete_signed_block_assumptions_reverse_helper(
    // //                     process.construct_complete_signed_block,
    // //                     process.dv_pubkey,
    // //                     dv.all_nodes,
    // //                     block_shares,
    // //                     data
    // //                 );

    // //             assert inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process);
    // //             assert block_shares <= dv.block_share_network.allMessagesSent;

    // //             var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(data.target.epoch));
    // //             var signing_root := compute_proposer_signing_root(data, fork_version);


    // //             var signers :=
    // //             set signer, block_share |
    // //                 && block_share in block_shares
    // //                 && signer in dv.all_nodes
    // //                 && verify_bls_signature(signing_root, block_share.signature, signer)
    // //             ::
    // //                 signer;

    // //             assert signers <= dv.all_nodes;

    // //             lemmaThereExistsAnHonestInQuorum(dv.all_nodes, dv.all_nodes - dv.honest_nodes_states.Keys, signers);

    // //             var h_s :| h_s in dv.honest_nodes_states.Keys && h_s in signers;
    // //             var h_s_att :| h_s_att in block_shares && verify_bls_signature(signing_root, h_s_att.signature, h_s);

    // //             assert
    // //             && h_s in dv.honest_nodes_states.Keys
    // //             && h_s_att in dv.block_share_network.allMessagesSent
    // //             && h_s_att.data == data
    // //             && verify_bls_signature(signing_root, h_s_att.signature, h_s);

    // //             assert
    // //             && h_s in dv.honest_nodes_states.Keys
    // //             && h_s_att in dv.block_share_network.allMessagesSent
    // //             && h_s_att.data == data
    // //             && verify_bls_signature(signing_root, h_s_att.signature, h_s);

    // //             assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(
    // //                 dv,
    // //                 h_s,
    // //                 h_s_att,
    // //                 aggregated_proposer
    // //             );

    // //             var state := f_add_new_submitted_block(process, aggregated_proposer);

    // //             forall a | a in state.bn.submitted_blocks
    // //             {
    // //                 assert exists hn', block_share: SignedBeaconBlock :: inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(dv, hn', block_share, a);
    // //             }
    // //             assert s' == state;
    // //         }
    // //     }
    // // }

    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    lemma lem_inv_all_in_transit_messages_were_sent_body_network_spec_next<M>(
        e: Network<M>,
        e': Network<M>,
        n: BLSPubkey,
        messagesToBeSent: set<MessaageWithRecipient<M>>,
        messagesReceived: set<M>
    )
    requires Block_Network_Spec.Next(e, e', n, messagesToBeSent, messagesReceived)
    requires inv_all_in_transit_messages_were_sent_body(e)
    ensures inv_all_in_transit_messages_were_sent_body(e')
    {}


    lemma lem_inv_all_in_transit_messages_were_sent_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.Event,
        dv': DVState
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
            Block_Network_Spec.Next<SignedBeaconBlock>(
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
        s: BlockConsensusInstance,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,
        s': BlockConsensusInstance,
        output: Optional<OutCommand>
    )
    requires Block_Consensus_Spec.Next(
                        s,
                        honest_nodes_validity_predicates,
                        s',
                        output
                    );
    ensures s.honest_nodes_validity_functions.Keys <= s'.honest_nodes_validity_functions.Keys;
    {
    }

    lemma  lem_NextConsensus_monotonic_set_of_validity_functions_2<D(!new, 0)>(
        s: BlockConsensusInstance,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,
        s': BlockConsensusInstance,
        output: Optional<OutCommand>,
        n: BLSPubkey
    )
    requires Block_Consensus_Spec.Next(
                        s,
                        honest_nodes_validity_predicates,
                        s',
                        output
                    );
    requires n in s.honest_nodes_validity_functions.Keys
    ensures s.honest_nodes_validity_functions[n] <= s'.honest_nodes_validity_functions[n];
    {
    }

    // // 1m 15s
    // TODO: Split this lemma into smaller pieces
    lemma lem_inv_decided_value_of_consensus_instance_is_decided_by_quorum_HonestNodeTakingStep(
        s: DVState,
        event: DV_Block_Proposer_Spec.Event,
        cid: Slot,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires event.HonestNodeTakingStep?
    requires cid in s'.consensus_instances_on_beacon_block.Keys
    requires inv_quorum_constraints(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_complete_signed_block(s)
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)
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

    lemma lem_inv_decided_value_of_consensus_instance_is_decided_by_quorum(
        s: DVState,
        event: DV_Block_Proposer_Spec.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')
    requires inv_quorum_constraints(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_complete_signed_block(s)
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)
    ensures inv_decided_value_of_consensus_instance_is_decided_by_quorum(s')
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

                forall cid |
                        && cid in s'.consensus_instances_on_beacon_block.Keys
                        && s'.consensus_instances_on_beacon_block[cid].decided_value.isPresent()
                ensures is_a_valid_decided_value(s'.consensus_instances_on_beacon_block[cid]);
                {
                    if s.consensus_instances_on_beacon_block[cid].decided_value.isPresent()
                    {
                        lem_inv_decided_value_of_consensus_instance_is_decided_by_quorum_HonestNodeTakingStep(s, event, cid, s');
                    }
                    else
                    {
                        assert is_a_valid_decided_value(s'.consensus_instances_on_beacon_block[cid]);
                    }
                }
                assert inv_decided_value_of_consensus_instance_is_decided_by_quorum(s');


            case AdversaryTakingStep(node, new_randao_shares_sent, new_block_shares_sent, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                assert inv_decided_value_of_consensus_instance_is_decided_by_quorum(s');
        }
    }

    lemma lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k_helper(
        s: DVState,
        cid: Slot
    )
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    requires inv_quorum_constraints(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires inv_only_dv_construct_complete_signed_block(s)
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
                inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(cid, proposer_duty, block_slashing_db, vp, complete_randao_reveal);

        assert s_consensus.decided_value.safe_get().slot == cid;
    }

    lemma lem_inv_all_in_transit_messages_were_sent_invNetwork(dv: DVState)
    requires inv_all_in_transit_messages_were_sent(dv)
    ensures invNetwork(dv)
    {}

    lemma lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k2(
        s: DVState
    )
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    requires inv_quorum_constraints(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires inv_only_dv_construct_complete_signed_block(s)
    ensures inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    {
        forall cid |
            && cid in s.consensus_instances_on_beacon_block.Keys
            && s.consensus_instances_on_beacon_block[cid].decided_value.isPresent()
        {
           lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k_helper(s, cid);
        }
    }

    // lemma lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    // requires inv_quorum_constraints(s)
    // requires inv_unchanged_paras_of_consensus_instances(s)
    // requires inv_only_dv_construct_complete_signed_block(s)
    // ensures inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s')
    // {
    //     lem_inv_quorum_constraints_dv_next(s, event, s');
    //     lem_inv_unchanged_paras_of_consensus_instances_dv_next(s, event, s');
    //     lem_inv_only_dv_construct_complete_signed_block_dv_next(s, event, s');
    //     lem_inv_decided_value_of_consensus_instance_is_decided_by_quorum(s, event, s');
    //     lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s, event, s');
    //     lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k2(s');
    // }

    // lemma lem_inv_rcvd_block_shares_are_in_all_sent_messages_dv_next(
    //     dv: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     dv': DVState
    // )
    // requires NextEventPreCond(dv, event)
    // requires NextEvent(dv, event, dv')
    // requires invNetwork(dv)
    // requires inv_rcvd_block_shares_are_in_all_sent_messages(dv)
    // ensures inv_rcvd_block_shares_are_in_all_sent_messages(dv')
    // {
    //     assert dv.block_share_network.allMessagesSent <= dv'.block_share_network.allMessagesSent;
    //     match event
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             var dvc := dv.honest_nodes_states[node];
    //             var dvc' := dv'.honest_nodes_states[node];
    //             match nodeEvent
    //             {
    //                 case ServeProposerDuty(proposer_duty) =>
    //                     lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_serve_proposer_duty(dv, dvc, proposer_duty, dvc');

    //                 case ReceiveRandaoShare(randao_share) =>
    //                     lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_listen_for_randao_shares(dv, dvc, randao_share, dvc');

    //                 case BlockConsensusDecided(id, decided_beacon_block) =>
    //                     if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
    //                     {
    //                         lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_block_consensus_decided(dv, dvc, id, decided_beacon_block, dvc');
    //                     }

    //                 case ReceiveSignedBeaconBlock(block_share) =>
    //                     assert multiset(addReceipientToMessages<SignedBeaconBlock>({block_share}, node)) <= dv.block_share_network.messagesInTransit;
    //                     assert MessaageWithRecipient(message := block_share, receipient := node) in dv.block_share_network.messagesInTransit;
    //                     assert block_share in dv.block_share_network.allMessagesSent;
    //                     lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_listen_for_block_signature_shares(dv, dvc, block_share, dvc');

    //                 case ImportedNewBlock(block) =>
    //                     var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
    //                     lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_listen_for_new_imported_blocks(dv, dvc, block, dvc');

    //                 case ResendRandaoRevealSignatureShare =>

    //                 case ResendBlockShare =>

    //                 case NoEvent =>

    //             }

    //         case AdversaryTakingStep(node, new_randao_shares_sent, new_block_shares_sent, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>

    //     }
    // }

    // lemma lem_inv_block_of_block_share_is_decided_value_helper(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires inv_block_of_block_share_is_decided_value(s)
    // requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    // requires inv_quorum_constraints(s)
    // requires same_honest_nodes_in_dv_and_ci(s)
    // requires inv_only_dv_construct_complete_signed_block(s)
    // requires |s.all_nodes| > 0
    // requires s'.block_share_network.allMessagesSent ==
    //                 s.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient({});
    // ensures  inv_block_of_block_share_is_decided_value(s');
    // {
    //     forall cid | cid in s.consensus_instances_on_beacon_block.Keys
    //     ensures && var s_consensus := s.consensus_instances_on_beacon_block[cid];
    //             && var s'_consensus := s'.consensus_instances_on_beacon_block[cid];
    //             && s_consensus.decided_value.isPresent() ==>
    //                     ( && s'_consensus.decided_value.isPresent()
    //                       && s_consensus.decided_value.safe_get() == s'_consensus.decided_value.safe_get()
    //                     )
    //         ;
    //     {
    //         var s_consensus := s.consensus_instances_on_beacon_block[cid];
    //         var s'_consensus := s'.consensus_instances_on_beacon_block[cid];

    //         assert isConditionForSafetyTrue(s_consensus);
    //         assert s_consensus.decided_value.isPresent() ==>
    //             && s'_consensus.decided_value.isPresent()
    //             && s_consensus.decided_value.safe_get() == s'_consensus.decided_value.safe_get()
    //         ;
    //     }

    //     assert forall cid | cid in s.consensus_instances_on_beacon_block.Keys ::
    //                 && var s_consensus := s.consensus_instances_on_beacon_block[cid];
    //                 && var s'_consensus := s'.consensus_instances_on_beacon_block[cid];
    //                 && s_consensus.decided_value.isPresent() ==>
    //                         ( && s'_consensus.decided_value.isPresent()
    //                         && s_consensus.decided_value.safe_get() == s'_consensus.decided_value.safe_get()
    //                         )
    //     ;

    //     var emptySet: set<MessaageWithRecipient<SignedBeaconBlock>> := {};
    //     calc {
    //         s'.block_share_network.allMessagesSent;
    //         ==
    //         s.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient(emptySet);
    //         ==
    //         {lem_getMessagesFromEmptySetOfMessagesWithRecipient_is_empty_set(emptySet);}
    //         s.block_share_network.allMessagesSent;
    //     }

    //     assert s'.block_share_network.allMessagesSent == s.block_share_network.allMessagesSent;

    //     forall hn, block_share |
    //             && hn in s'.honest_nodes_states.Keys
    //             && block_share in s'.block_share_network.allMessagesSent
    //             && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(block_share.block.target.epoch));
    //             && var proposer_signing_root := compute_proposer_signing_root(block_share.block, fork_version);
    //             && verify_bls_signature(proposer_signing_root, block_share.signature, hn)
    //     ensures inv_block_of_block_share_is_decided_value_body(s', block_share);
    //     {
    //         assert block_share in s.block_share_network.allMessagesSent;
    //         assert inv_block_of_block_share_is_decided_value_body(s, block_share);
    //         assert inv_block_of_block_share_is_decided_value_body(s', block_share);
    //     }

    //     assert inv_block_of_block_share_is_decided_value(s');
    // }

    // lemma lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_ex_f_listen_for_block_signature_shares(
    //     process: DVCState,
    //     block_share: SignedBeaconBlock,
    //     s': DVCState,
    //     dv: DVState
    // )
    // requires f_listen_for_block_signature_shares.requires(process, block_share)
    // requires s' == f_listen_for_block_signature_shares(process, block_share).state
    // requires construct_complete_signed_block_assumptions_helper(
    //             process.construct_complete_signed_block,
    //             process.dv_pubkey,
    //             dv.all_nodes
    //         )
    // requires inv_quorum_constraints(dv)
    // requires block_share in dv.block_share_network.allMessagesSent
    // requires inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process)
    // // ensures forall block | block in f_listen_for_block_signature_shares(process, block_share).outputs.submitted_blocks
    // //                     ::
    // //                     exists hn', block_share: SignedBeaconBlock
    // //                         ::
    // //                         inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(dv, hn', block_share, block);
    // {
    //     var slot := block_share.block.slot;

    //     if is_slot_for_current_or_future_instances(process, slot)
    //     {
    //          var data := block_share.block;
    //         var rcvd_block_shares_db_at_slot := getOrDefault(process.rcvd_block_shares, slot, map[]);
    //         var process_with_new_block_share :=
    //             process.(
    //                 rcvd_block_shares :=
    //                     process.rcvd_block_shares[
    //                         slot :=
    //                             rcvd_block_shares_db_at_slot[
    //                                 data :=
    //                                     getOrDefault(rcvd_block_shares_db_at_slot, data, {}) +
    //                                     {block_share}
    //                                 ]
    //                     ]
    //             );

    //         if process.construct_complete_signed_block(process_with_new_block_share.rcvd_block_shares[slot][data]).isPresent()
    //         {
    //             var block_shares := process_with_new_block_share.rcvd_block_shares[slot][data];
    //             var complete_signed_block := process.construct_complete_signed_block(block_shares).safe_get();
    //             var signing_root := compute_block_signing_root(complete_signed_block.block);

    //             assert construct_complete_signed_block_assumptions_reverse(
    //                         process.construct_complete_signed_block,
    //                         process.dv_pubkey,
    //                         dv.all_nodes
    //                     );

    //             assert signed_beacon_block_signer_threshold(dv.all_nodes, block_shares, signing_root);



    //             // var signers :=
    //             //     set signer, block_share |
    //             //         && block_share in block_shares
    //             //         && signer in dv.all_nodes
    //             //         && verify_bls_signature(signing_root, block_share.signature, signer)
    //             //     ::
    //             //         signer;

    //             // assert signers <= dv.all_nodes;

    //             // assert signed_beacon_block_signer_threshold(dv.all_nodes, block_shares, signing_root);

    //             // lemmaThereExistsAnHonestInQuorum(dv.all_nodes, dv.all_nodes - dv.honest_nodes_states.Keys, signers);

    //         //     var h_s :| h_s in dv.honest_nodes_states.Keys && h_s in signers;
    //         //     var h_s_att :| h_s_att in block_shares && verify_bls_signature(signing_root, h_s_att.signature, h_s);

    //         //     assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(
    //         //                     dv,
    //         //                     h_s,
    //         //                     h_s_att,
    //         //                     aggregated_proposer
    //         //                 );

    //         //     assert f_listen_for_block_signature_shares(process, block_share).outputs.submitted_blocks == {aggregated_proposer};

    //         //     assert forall a | a in f_listen_for_block_signature_shares(process, block_share).outputs.submitted_blocks ::
    //         //                 exists hn', block_share: SignedBeaconBlock :: inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(dv, hn', block_share, a);
    //         }
    //     }
    // }



    // lemma lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_ex_helper(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s)
    // requires s'.all_blocks_created == s.all_blocks_created
    // ensures inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s');
    // {
    //     forall a |
    //         && a in s'.all_blocks_created
    //         && is_valid_proposer(a, s'.dv_pubkey)
    //     ensures exists hn', block_share: SignedBeaconBlock :: inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s', hn', block_share, a);
    //     {
    //         var hn', block_share: SignedBeaconBlock :|
    //             inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s, hn', block_share, a);

    //         assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s', hn', block_share, a);
    //         assert exists hn', block_share: SignedBeaconBlock :: inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s', hn', block_share, a);
    //     }
    // }

    // lemma lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_dv_next_ReceivedSignedBeaconBlock(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires event.HonestNodeTakingStep?
    // requires event.event.ReceivedSignedBeaconBlock?
    // requires inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s)
    // requires construct_complete_signed_block_assumptions_helper(
    //     s.construct_complete_signed_block,
    //     s.dv_pubkey,
    //     s.all_nodes
    // )
    // requires inv_only_dv_construct_complete_signed_block(s)
    // requires invNetwork(s)
    // requires inv_quorum_constraints(s)
    // requires inv_rcvd_block_shares_are_in_all_messages_sent(s)
    // ensures inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s')
    // {
    //     assert s.block_share_network.allMessagesSent <= s'.block_share_network.allMessagesSent;
    //     match event
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             var s_node := s.honest_nodes_states[node];
    //             var s'_node := s'.honest_nodes_states[node];
    //             match nodeEvent
    //             {
    //                 case ReceivedSignedBeaconBlock(block_share) =>
    //                     assert multiset(addReceipientToMessages<SignedBeaconBlock>({block_share}, node)) <= s.block_share_network.messagesInTransit;

    //                     assert MessaageWithRecipient(message := block_share, receipient := node) in s.block_share_network.messagesInTransit;

    //                     var stateAndOutput := f_listen_for_block_signature_shares(s_node, block_share);


    //                     assert block_share in s.block_share_network.allMessagesSent;
    //                     assert s'.all_blocks_created == s.all_blocks_created + stateAndOutput.outputs.submitted_blocks;

    //                     lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_ex_f_listen_for_block_signature_shares(
    //                         s_node,
    //                         block_share,
    //                         s'_node,
    //                         s
    //                     );

    //                     forall a |
    //                                 && a in s'.all_blocks_created
    //                                 && is_valid_proposer(a, s'.dv_pubkey)
    //                     ensures exists hn', block_share: SignedBeaconBlock :: inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s', hn', block_share, a);
    //                     {
    //                         if a in s.all_blocks_created
    //                         {
    //                             var hn', block_share: SignedBeaconBlock :| inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s, hn', block_share, a);
    //                             assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s', hn', block_share, a);
    //                         }
    //                         else
    //                         {
    //                             assert a in stateAndOutput.outputs.submitted_blocks;
    //                             var hn', block_share: SignedBeaconBlock :| inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s, hn', block_share, a);
    //                             assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s', hn', block_share, a);
    //                         }
    //                     }

    //                     assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s');
    //             }
    //     }
    // }

    // lemma lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_dv_next_AdversaryTakingStep(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires event.AdversaryTakingStep?
    // requires inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s)
    // requires construct_complete_signed_block_assumptions_helper(
    //     s.construct_complete_signed_block,
    //     s.dv_pubkey,
    //     s.all_nodes
    // )
    // requires inv_only_dv_construct_complete_signed_block(s)
    // requires invNetwork(s)
    // requires inv_quorum_constraints(s)
    // requires inv_rcvd_block_shares_are_in_all_messages_sent(s)
    // ensures inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s')
    // {
    //     assert s.block_share_network.allMessagesSent <= s'.block_share_network.allMessagesSent;
    //     match event
    //     {
    //         case AdversaryTakingStep(node, new_randao_shares_sent, new_block_shares_sent, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
    //             forall a |
    //                 && a in s'.all_blocks_created
    //                 && is_valid_proposer(a, s'.dv_pubkey)
    //             ensures exists hn', block_share: SignedBeaconBlock :: inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s', hn', block_share, a);
    //             {
    //                 if a in s.all_blocks_created
    //                 {
    //                     var hn', block_share: SignedBeaconBlock :| inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s, hn', block_share, a);
    //                     assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(s', hn', block_share, a);
    //                 }
    //                 else
    //                 {
    //                     var block_shares :|
    //                         && block_shares <= s'.block_share_network.allMessagesSent
    //                         // && var sig_shares := set x | x in block_shares :: x.signature;
    //                         && var constructed_sig := s.construct_complete_signed_block(block_shares);
    //                         && constructed_sig.isPresent()
    //                         && constructed_sig.safe_get() == a.signature
    //                         ;

    //                     var constructed_sig := s.construct_complete_signed_block(block_shares);

    //                     var data: BeaconBlock :|
    //                         construct_complete_signed_block_assumptions_reverse_helper(
    //                             s.construct_complete_signed_block,
    //                             s.dv_pubkey,
    //                             s.all_nodes,
    //                             block_shares,
    //                             data
    //                         );

    //                     var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(data.target.epoch));
    //                     var signing_root := compute_proposer_signing_root(data, fork_version);


    //                     var signers :=
    //                     set signer, block_share |
    //                         && block_share in block_shares
    //                         && signer in s.all_nodes
    //                         && verify_bls_signature(signing_root, block_share.signature, signer)
    //                     ::
    //                         signer;

    //                     assert signers <= s.all_nodes;

    //                     lemmaThereExistsAnHonestInQuorum(s.all_nodes, s.all_nodes - s.honest_nodes_states.Keys, signers);

    //                     var h_s :| h_s in s.honest_nodes_states.Keys && h_s in signers;
    //                     var h_s_att :| h_s_att in block_shares && verify_bls_signature(signing_root, h_s_att.signature, h_s);

    //                     assert
    //                     && h_s in s.honest_nodes_states.Keys
    //                     && h_s_att in s.block_share_network.allMessagesSent
    //                     && h_s_att.data == data
    //                     && verify_bls_signature(signing_root, h_s_att.signature, h_s);

    //                     assert
    //                     && h_s in s.honest_nodes_states.Keys
    //                     && h_s_att in s.block_share_network.allMessagesSent
    //                     && h_s_att.data == data
    //                     && verify_bls_signature(signing_root, h_s_att.signature, h_s);

    //                     compute_signing_root_properties<BeaconBlock>();
    //                     lem_verify_bls_signature();

    //                     var a_fork_version := bn_get_fork_version(compute_start_slot_at_epoch(a.data.target.epoch));
    //                     var a_proposer_signing_root := compute_proposer_signing_root(a.data, a_fork_version);

    //                     assert verify_bls_signature(signing_root, a.signature, s'.dv_pubkey);

    //                     assert verify_bls_signature(a_proposer_signing_root, a.signature, s'.dv_pubkey);

    //                     assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(
    //                         s,
    //                         h_s,
    //                         h_s_att,
    //                         a
    //                     );

    //                     assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(
    //                         s',
    //                         h_s,
    //                         h_s_att,
    //                         a
    //                     );
    //                 }
    //             }
    //             assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s');
    //     }
    // }

    // lemma lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_dv_next(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s)
    // requires construct_complete_signed_block_assumptions_helper(
    //     s.construct_complete_signed_block,
    //     s.dv_pubkey,
    //     s.all_nodes
    // )
    // requires inv_only_dv_construct_complete_signed_block(s)
    // requires invNetwork(s)
    // requires inv_quorum_constraints(s)
    // requires inv_rcvd_block_shares_are_in_all_messages_sent(s)
    // ensures inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s')
    // {
    //     assert s.block_share_network.allMessagesSent <= s'.block_share_network.allMessagesSent;
    //     match event
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             var s_node := s.honest_nodes_states[node];
    //             var s'_node := s'.honest_nodes_states[node];
    //             match nodeEvent
    //             {
    //                 case ServeProposerDuty(proposer_duty) =>
    //                     lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_ex_helper(s, event, s');
    //                     assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s');

    //                 case ReceiveRandaoShare(randao_share) =>

    //                 case BlockConsensusDecided(id, decided_beacon_block) =>
    //                     lem_f_block_consensus_decided_unchanged_dvc_vars(s.honest_nodes_states[node], id, decided_beacon_block, s'.honest_nodes_states[node]);
    //                     lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_ex_helper(s, event, s');
    //                     assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s');

    //                  case ReceiveSignedBeaconBlock(block_share) =>
    //                     lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_dv_next_ReceivedSignedBeaconBlock(
    //                         s,
    //                         event,
    //                         s'
    //                     );

    //                 case ImportedNewBlock(block) =>
    //                     var s_node := f_add_block_to_bn(s_node, nodeEvent.block);
    //                     lem_f_listen_for_new_imported_blocks_unchanged_dvc_vars(s_node, block, s'_node);
    //                     assert s'.all_blocks_created == s.all_blocks_created;
    //                     lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_ex_helper(s, event, s');
    //                     assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s');

    //                 case ResendSignedBeaconBlocks =>
    //                     assert s'.all_blocks_created == s.all_blocks_created;
    //                     lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_ex_helper(s, event, s');
    //                     assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s');

    //                 case NoEvent =>
    //                     assert s'.all_blocks_created == s.all_blocks_created;
    //                     lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_ex_helper(s, event, s');
    //                     assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s');
    //             }

    //         case AdversaryTakingStep(node, new_randao_shares_sent, new_block_shares_sent, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
    //             lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_dv_next_AdversaryTakingStep(
    //                 s,
    //                 event,
    //                 s'
    //             );
    //     }
    // }

    // lemma lem_inv_rcvd_block_shares_are_in_all_messages_sent(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires invNetwork(s)
    // requires inv_rcvd_block_shares_are_in_all_messages_sent(s)
    // ensures inv_rcvd_block_shares_are_in_all_messages_sent(s')
    // {
    //     match event
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             var s_node := s.honest_nodes_states[node];
    //             var s'_node := s'.honest_nodes_states[node];
    //             match nodeEvent
    //             {
    //                 case ServeProposerDuty(proposer_duty) =>
    //                     lem_f_serve_proposer_duty_unchanged_vars(s_node, proposer_duty, s'_node);

    //                 case BlockConsensusDecided(id, decided_beacon_block) =>
    //                     lem_f_block_consensus_decided_unchanged_dvc_vars(s_node, id, decided_beacon_block, s'_node);

    //                 case ReceivedSignedBeaconBlock(block_share) =>
    //                     assert multiset(addReceipientToMessages<SignedBeaconBlock>({block_share}, node)) <= s.block_share_network.messagesInTransit;
    //                     assert MessaageWithRecipient(message := block_share, receipient := node) in s.block_share_network.messagesInTransit;
    //                     assert block_share in s.block_share_network.allMessagesSent;
    //                     lem_inv_rcvd_block_shares_are_in_all_messages_sent_f_listen_for_block_signature_shares(
    //                         s_node,
    //                         block_share,
    //                         s'_node,
    //                         s
    //                     );

    //                 case ImportedNewBlock(block) =>
    //                     var s_node := f_add_block_to_bn(s_node, nodeEvent.block);
    //                     lem_f_listen_for_new_imported_blocks_unchanged_dvc_vars(s_node, block, s'_node);
    //                     assert inv_rcvd_block_shares_are_in_all_messages_sent(s');

    //                 case ResendSignedBeaconBlocks =>
    //                     assert inv_rcvd_block_shares_are_in_all_messages_sent(s');
    //                 case NoEvent =>

    //             }

    //         case AdversaryTakingStep(node, new_randao_shares_sent, new_block_shares_sent, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>

    //     }
    // }

    // lemma lem_getMessagesFromEmptySetOfMessagesWithRecipient_is_empty_set<M>(mswr: set<MessaageWithRecipient<M>>)
    // requires mswr == {}
    // ensures getMessagesFromMessagesWithRecipient(mswr) == {}
    // {
    // }



    // lemma lem_consensus_next_under_safety<D(!new, 0)>(
    //     s: BlockConsensusInstance,
    //     honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,
    //     s': BlockConsensusInstance,
    //     output: Optional<OutCommand>
    // )
    // requires Block_Consensus_Spec.Next(s, honest_nodes_validity_predicates, s', output)
    // requires isConditionForSafetyTrue(s)
    // requires s.decided_value.isPresent()
    // ensures s'.decided_value.isPresent()
    // ensures s.decided_value.safe_get() == s'.decided_value.safe_get()
    // { }

    // lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_get_s_w_honest_node_states_updated(
    //     s: DVState,
    //     node: BLSPubkey,
    //     nodeEvent: Block_Types.Event
    // ) returns (s_w_honest_node_states_updated: DVState)
    // requires node in s.honest_nodes_states
    // ensures s_w_honest_node_states_updated == add_block_to_bn_with_event(s, node, nodeEvent)
    // ensures s_w_honest_node_states_updated == s.(honest_nodes_states := s_w_honest_node_states_updated.honest_nodes_states)
    // ensures s_w_honest_node_states_updated.honest_nodes_states == s.honest_nodes_states[node := s_w_honest_node_states_updated.honest_nodes_states[node]]
    // ensures s_w_honest_node_states_updated.honest_nodes_states[node] == s.honest_nodes_states[node].(bn := s_w_honest_node_states_updated.honest_nodes_states[node].bn)
    // {
    //     s_w_honest_node_states_updated :=
    //         if nodeEvent.ImportedNewBlock? then
    //             s.(
    //                 honest_nodes_states := s.honest_nodes_states[node := f_add_block_to_bn(s.honest_nodes_states[node], nodeEvent.block)]
    //             )
    //         else
    //             s
    //         ;
    // }

   

    // lemma lem_inv_block_of_block_share_is_decided_value_proposer_consensus_decided_helper_2(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires event.HonestNodeTakingStep?
    // requires event.event.BlockConsensusDecided?
    // requires inv_quorum_constraints(s)
    // requires inv_unchanged_paras_of_consensus_instances(s)
    // requires |s.all_nodes| > 0
    // ensures s'.consensus_instances_on_beacon_block[event.event.id].decided_value.safe_get() == event.event.decided_beacon_block;
    // {
    //     match event
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             var s_node := s.honest_nodes_states[node];
    //             var s'_node := s'.honest_nodes_states[node];
    //             match nodeEvent
    //             {
    //                 case BlockConsensusDecided(id: Slot, decided_beacon_block) =>
    //                     var s_w_honest_node_states_updated := lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_get_s_w_honest_node_states_updated(s, node, nodeEvent);
    //                     var cid := id;

    //                     assert s_w_honest_node_states_updated.consensus_instances_on_beacon_block == s.consensus_instances_on_beacon_block;

    //                     var output := Some(Decided(node, nodeEvent.decided_beacon_block));

    //                     var validityPredicates :=
    //                             map n |
    //                                     && n in s_w_honest_node_states_updated.honest_nodes_states.Keys
    //                                     && cid in s_w_honest_node_states_updated.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys
    //                                 ::
    //                                     s_w_honest_node_states_updated.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid].validityPredicate
    //                             ;

    //                     var s_consensus := s_w_honest_node_states_updated.consensus_instances_on_beacon_block[cid];
    //                     var s'_consensus := s'.consensus_instances_on_beacon_block[cid];

    //                     assert Block_Consensus_Spec.Next(
    //                                 s_consensus,
    //                                 validityPredicates,
    //                                 s'_consensus,
    //                                 output
    //                             );

    //                     assert s'.consensus_instances_on_beacon_block[id].decided_value.isPresent();
    //                     assert isConditionForSafetyTrue(s'_consensus);
    //                     assert s'_consensus.decided_value.safe_get() == decided_beacon_block;
    //                     assert s'.consensus_instances_on_beacon_block[id].decided_value.safe_get() == decided_beacon_block;
    //             }
    //     }
    // }







    // lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_get_s_w_honest_node_states_updated_2(
    //     s: DVState,
    //     node: BLSPubkey,
    //     nodeEvent: Block_Types.Event,
    //     node': BLSPubkey,
    //     s_w_honest_node_states_updated: DVState
    // )
    // requires node in s.honest_nodes_states
    // requires node' in s.honest_nodes_states
    // requires s_w_honest_node_states_updated == add_block_to_bn_with_event(s, node, nodeEvent)
    // ensures s_w_honest_node_states_updated.honest_nodes_states[node'].block_consensus_engine_state == s.honest_nodes_states[node'].block_consensus_engine_state
    // {
    // }

    // lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_helper(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState,
    //     cid: Slot,
    //     hn: BLSPubkey,
    //     vp: BeaconBlock -> bool
    // )   returns (proposer_duty: ProposerDuty, block_slashing_db: set<SlashingDBBlock>)
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires inv_quorum_constraints(s)
    // requires inv_unchanged_paras_of_consensus_instances(s)
    // requires inv_only_dv_construct_complete_signed_block(s)
    // requires
    //         && hn in s'.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions.Keys
    //         && vp in s'.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions[hn]
    // requires event.HonestNodeTakingStep?
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    // ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(cid, proposer_duty, block_slashing_db, vp);
    // {
    //     assert s.block_share_network.allMessagesSent <= s'.block_share_network.allMessagesSent;
    //     match event
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             var s_node := s.honest_nodes_states[node];
    //             var s'_node := s'.honest_nodes_states[node];

    //             var s_w_honest_node_states_updated :=
    //                 lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_get_s_w_honest_node_states_updated(s, node, nodeEvent);

    //             assert s_w_honest_node_states_updated.consensus_instances_on_beacon_block == s.consensus_instances_on_beacon_block;


    //             var output :=
    //                 if nodeEvent.BlockConsensusDecided? && nodeEvent.id == cid then
    //                     Some(Decided(node, nodeEvent.decided_beacon_block))
    //                 else
    //                     None
    //                 ;

    //             var validityPredicates :=
    //                 map n |
    //                         && n in s_w_honest_node_states_updated.honest_nodes_states.Keys
    //                         && cid in s_w_honest_node_states_updated.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys
    //                     ::
    //                         s_w_honest_node_states_updated.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid].validityPredicate
    //                 ;

    //             var s_consensus := s_w_honest_node_states_updated.consensus_instances_on_beacon_block[cid];
    //             var s'_consensus := s'.consensus_instances_on_beacon_block[cid];

    //             assert
    //                 Block_Consensus_Spec.Next(
    //                     s_consensus,
    //                     validityPredicates,
    //                     s'_consensus,
    //                     output
    //                 );

    //         if hn in s_consensus.honest_nodes_validity_functions.Keys  && vp in s_consensus.honest_nodes_validity_functions[hn]
    //         {
    //             assert vp in s'_consensus.honest_nodes_validity_functions[hn];

    //             proposer_duty, block_slashing_db :| inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(cid, proposer_duty, block_slashing_db, vp);

    //         }
    //         else
    //         {
    //             assert vp in validityPredicates.Values;
    //             var vpn :| vpn in validityPredicates.Keys && validityPredicates[vpn] == vp;
    //             assert validityPredicates[vpn] == s_w_honest_node_states_updated.honest_nodes_states[vpn].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid].validityPredicate;

    //             assert vpn in s.honest_nodes_states.Keys;
    //             assert cid in s_w_honest_node_states_updated.honest_nodes_states[vpn].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys;

    //             lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_get_s_w_honest_node_states_updated_2(s, node, nodeEvent, vpn, s_w_honest_node_states_updated);

    //             assert s_w_honest_node_states_updated.honest_nodes_states[vpn].block_consensus_engine_state == s.honest_nodes_states[vpn].block_consensus_engine_state;
    //             assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc(s, vpn, cid);

    //             proposer_duty, block_slashing_db :| inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(cid, proposer_duty, block_slashing_db, vp);
    //         }

    //         assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(cid, proposer_duty, block_slashing_db, vp);
    //     }

    // }

    // lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    // requires inv_quorum_constraints(s)
    // requires inv_unchanged_paras_of_consensus_instances(s)
    // requires inv_only_dv_construct_complete_signed_block(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    // ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s')
    // {
    //     match event
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             forall hn, cid: Slot, vp |
    //                 && hn in s'.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions.Keys
    //                 && vp in s'.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions[hn]
    //             ensures exists proposer_duty, block_slashing_db :: inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(cid, proposer_duty, block_slashing_db, vp)
    //             {
    //                 var proposer_duty: ProposerDuty, block_slashing_db := lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_helper(s, event, s', cid, hn, vp);
    //             }
    //             assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s');

    //         case AdversaryTakingStep(node, new_randao_shares_sent, new_block_shares_sent, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
    //             assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s');
    //     }
    // }





    // lemma lem_inv_block_of_block_share_is_decided_value_proposer_consensus_decided_with_decided_data_for_current_slot(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState,
    //     node: BLSPubkey,
    //     nodeEvent: Block_Types.Event,
    //     nodeOutputs: Outputs,
    //     id: Slot,
    //     decided_beacon_block: BeaconBlock
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires event.HonestNodeTakingStep?
    // requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    // requires nodeEvent.BlockConsensusDecided?
    // requires nodeEvent == BlockConsensusDecided(id, decided_beacon_block)
    // requires inv_block_of_block_share_is_decided_value(s)
    // requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    // requires inv_block_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)
    // requires inv_quorum_constraints(s)
    // requires inv_unchanged_paras_of_consensus_instances(s)
    // requires same_honest_nodes_in_dv_and_ci(s)
    // requires inv_only_dv_construct_complete_signed_block(s)
    // requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    // requires |s.all_nodes| > 0
    // requires && var process := s.honest_nodes_states[node];
    //          && is_decided_data_for_current_slot(process, decided_beacon_block, id)
    // ensures inv_block_of_block_share_is_decided_value(s')
    // {
    //     var process := s.honest_nodes_states[node];
    //     var process' := s'.honest_nodes_states[node];

    //     var proposer_with_signature_share :=
    //         f_calc_proposer_with_sign_share_from_decided_beacon_block(
    //             process,
    //             id,
    //             decided_beacon_block
    //         );
    //     var messagesToBeSent := f_block_consensus_decided(process, id, decided_beacon_block).outputs.block_shares_sent;

    //     assert messagesToBeSent ==  multicast(proposer_with_signature_share, process.peers);
    //     assert s'.block_share_network.allMessagesSent ==
    //                 s.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent);
    //     assert forall m | m in messagesToBeSent :: m.message == proposer_with_signature_share;

    //     lemmaOnGetMessagesFromMessagesWithRecipientWhenAllMessagesAreTheSame(messagesToBeSent, proposer_with_signature_share);
    //     assert getMessagesFromMessagesWithRecipient(messagesToBeSent) ==  {proposer_with_signature_share};
    //     assert s'.block_share_network.allMessagesSent ==
    //                 s.block_share_network.allMessagesSent + { proposer_with_signature_share };

    //     forall hn, block_share |
    //             && hn in s'.honest_nodes_states.Keys
    //             && block_share in s'.block_share_network.allMessagesSent
    //             && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(block_share.block.target.epoch));
    //             && var proposer_signing_root := compute_proposer_signing_root(block_share.block, fork_version);
    //             && verify_bls_signature(proposer_signing_root, block_share.signature, hn)
    //     ensures s'.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.isPresent();
    //     ensures s'.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.safe_get() == block_share.block;
    //     {
    //         if block_share in s.block_share_network.allMessagesSent
    //         {
    //             lem_inv_block_of_block_share_is_decided_value_proposer_consensus_decided_helper_1(s, event, s', hn, block_share);
    //         }
    //         else
    //         {
    //             assert block_share == proposer_with_signature_share;
    //             lemmaImaptotalElementInDomainIsInKeys(s.consensus_instances_on_beacon_block, id);
    //             assert id in s.consensus_instances_on_beacon_block.Keys ;
    //             lem_inv_block_of_block_share_is_decided_value_proposer_consensus_decided_helper_2(s, event, s');

    //             assert s'.consensus_instances_on_beacon_block[id].decided_value.safe_get() == decided_beacon_block;
    //             assert s'.consensus_instances_on_beacon_block[id].decided_value.safe_get() == block_share.block;
    //             lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s, event, s');

    //             assert block_share.block.slot == id;
    //             assert s'.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.isPresent();
    //             assert s'.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.safe_get() == block_share.block;
    //         }
    //     }

    //     assert inv_block_of_block_share_is_decided_value(s');
    // }

    // lemma lem_inv_block_of_block_share_is_decided_value_proposer_consensus_decided_without_decided_data_for_current_slot(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState,
    //     node: BLSPubkey,
    //     nodeEvent: Block_Types.Event,
    //     nodeOutputs: Outputs,
    //     id: Slot,
    //     decided_beacon_block: BeaconBlock
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires event.HonestNodeTakingStep?
    // requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    // requires nodeEvent.BlockConsensusDecided?
    // requires nodeEvent == BlockConsensusDecided(id, decided_beacon_block)
    // requires inv_block_of_block_share_is_decided_value(s)
    // requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    // requires inv_block_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)
    // requires inv_quorum_constraints(s)
    // requires inv_unchanged_paras_of_consensus_instances(s)
    // requires same_honest_nodes_in_dv_and_ci(s)
    // requires inv_only_dv_construct_complete_signed_block(s)
    // requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    // requires |s.all_nodes| > 0
    // requires && var process := s.honest_nodes_states[node];
    //          && !is_decided_data_for_current_slot(process, decided_beacon_block, id)
    // ensures inv_block_of_block_share_is_decided_value(s')
    // {
    //     forall hn, block_share |
    //             && hn in s'.honest_nodes_states.Keys
    //             && block_share in s'.block_share_network.allMessagesSent
    //             && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(block_share.block.target.epoch));
    //             && var proposer_signing_root := compute_proposer_signing_root(block_share.block, fork_version);
    //             && verify_bls_signature(proposer_signing_root, block_share.signature, hn)
    //     ensures s'.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.isPresent();
    //     ensures s'.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.safe_get() == block_share.block;
    //     {
    //         assert block_share in s.block_share_network.allMessagesSent;
    //         lem_inv_block_of_block_share_is_decided_value_proposer_consensus_decided_helper_1(s, event, s', hn, block_share);
    //     }

    //     assert inv_block_of_block_share_is_decided_value(s');
    // }

    // lemma lem_inv_block_of_block_share_is_decided_value_proposer_consensus_decided(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires event.HonestNodeTakingStep?
    // requires event.event.BlockConsensusDecided?
    // requires inv_block_of_block_share_is_decided_value(s)
    // requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    // requires inv_block_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)
    // requires inv_quorum_constraints(s)
    // requires inv_unchanged_paras_of_consensus_instances(s)
    // requires same_honest_nodes_in_dv_and_ci(s)
    // requires inv_only_dv_construct_complete_signed_block(s)
    // requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    // requires |s.all_nodes| > 0
    // ensures inv_block_of_block_share_is_decided_value(s')
    // {
    //     match event
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             var process := s.honest_nodes_states[node];
    //             var process' := s'.honest_nodes_states[node];
    //             match nodeEvent
    //             {
    //                 case BlockConsensusDecided(id: Slot, decided_beacon_block) =>
    //                     if  && process.current_proposer_duty.isPresent()
    //                         && id == process.current_proposer_duty.safe_get().slot
    //                         && id == decided_beacon_block.slot
    //                     {
    //                         lem_inv_block_of_block_share_is_decided_value_proposer_consensus_decided_with_decided_data_for_current_slot(
    //                             s,
    //                             event,
    //                             s',
    //                             node,
    //                             nodeEvent,
    //                             nodeOutputs,
    //                             id,
    //                             decided_beacon_block
    //                         );
    //                     }
    //                     else
    //                     {
    //                         lem_inv_block_of_block_share_is_decided_value_proposer_consensus_decided_without_decided_data_for_current_slot(
    //                             s,
    //                             event,
    //                             s',
    //                             node,
    //                             nodeEvent,
    //                             nodeOutputs,
    //                             id,
    //                             decided_beacon_block
    //                         );
    //                     }
    //             }
    //     }
    // }

    // lemma lem_inv_block_of_block_share_is_decided_value_proposer_adversary(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires event.AdversaryTakingStep?
    // requires inv_block_of_block_share_is_decided_value(s)
    // requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    // requires inv_block_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)
    // requires inv_quorum_constraints(s)
    // requires same_honest_nodes_in_dv_and_ci(s)
    // requires inv_only_dv_construct_complete_signed_block(s)
    // requires |s.all_nodes| > 0
    // ensures inv_block_of_block_share_is_decided_value(s')
    // {
    //     var new_block_shares_sent := s'.block_share_network.allMessagesSent - s.block_share_network.allMessagesSent;

    //     forall hn, block_share |
    //             && hn in s'.honest_nodes_states.Keys
    //             && block_share in s'.block_share_network.allMessagesSent
    //             && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(block_share.block.target.epoch));
    //             && var proposer_signing_root := compute_proposer_signing_root(block_share.block, fork_version);
    //             && verify_bls_signature(proposer_signing_root, block_share.signature, hn)
    //     ensures s'.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.isPresent();
    //     ensures s'.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.safe_get() == block_share.block;
    //     {
    //         var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(block_share.block.target.epoch));
    //         var proposer_signing_root := compute_proposer_signing_root(block_share.block, fork_version);

    //         if block_share in s.block_share_network.allMessagesSent
    //         {
    //             assert s.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.isPresent();
    //             assert s.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.safe_get() == block_share.block;
    //         }
    //         else
    //         {
    //             forall signer | verify_bls_signature(proposer_signing_root, block_share.signature, signer)
    //             ensures signer in s.adversary.nodes;
    //             ensures signer !in  s.honest_nodes_states.Keys;
    //             {

    //                 assert signer in s.adversary.nodes;
    //                 lemmaEmptyIntersectionImpliesDisjointness(s.adversary.nodes, s.honest_nodes_states.Keys);
    //                 assert s.adversary.nodes !! s.honest_nodes_states.Keys;
    //                 assert signer !in  s.honest_nodes_states.Keys;
    //             }
    //             assert false;
    //         }
    //     }

    //     assert inv_block_of_block_share_is_decided_value(s');
    // }

    // lemma lem_inv_block_of_block_share_is_decided_value_helper2<M>(
    //     allMessagesSent': set<M>,
    //     allMessagesSent: set<M>,
    //     messagesToBeSent: set<MessaageWithRecipient<M>>
    // )
    // requires allMessagesSent' == allMessagesSent +
    //                             getMessagesFromMessagesWithRecipient(messagesToBeSent);
    // requires messagesToBeSent == {}
    // ensures allMessagesSent' == allMessagesSent
    // { }



    // lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_updateBlockConsensusInstanceValidityCheckHelper(
    //     m: map<Slot, BlockConsensusValidityCheckState>,
    //     new_block_slashing_db: set<SlashingDBBlock>,
    //     m': map<Slot, BlockConsensusValidityCheckState>
    // )
    // requires m' == updateBlockConsensusInstanceValidityCheckHelper(m, new_block_slashing_db)
    // requires forall k | k in m :: inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2_body_body(k, m[k].proposer_duty, m[k].validityPredicate)
    // ensures forall k | k in m' :: inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2_body_body(k, m'[k].proposer_duty, m'[k].validityPredicate)
    // {
    //     forall k | k in  m
    //     ensures k in m'
    //     {
    //         lemmaMapKeysHasOneEntryInItems(m, k);
    //         assert k in m';
    //     }

    //     assert m.Keys == m'.Keys;

    //     forall k | k in m'
    //     ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(k, m'[k].proposer_duty, new_block_slashing_db, m'[k].validityPredicate);
    //     {
    //         assert m'[k] == m[k].(
    //                 validityPredicate := (ad: BeaconBlock) => ci_decision_is_valid_beacon_block(new_block_slashing_db, ad, m[k].proposer_duty)
    //         );
    //         assert  inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(k, m'[k].proposer_duty, new_block_slashing_db, m'[k].validityPredicate);
    //     }
    // }


    // lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_duty_updateBlockConsensusInstanceValidityCheck(
    //     s: BlockConsensusEngineState,
    //     new_block_slashing_db: set<SlashingDBBlock>,
    //     s': BlockConsensusEngineState
    // )
    // requires s' == updateBlockConsensusInstanceValidityCheck(s, new_block_slashing_db)
    // ensures s'.active_consensus_instances_on_beacon_blocks.Keys == s.active_consensus_instances_on_beacon_blocks.Keys
    // ensures s'.block_slashing_db_hist.Keys == s.block_slashing_db_hist.Keys + s'.active_consensus_instances_on_beacon_blocks.Keys;
    // {
    //     lem_updateBlockConsensusInstanceValidityCheckHelper(s.active_consensus_instances_on_beacon_blocks, new_block_slashing_db, s'.active_consensus_instances_on_beacon_blocks);

    //     assert s'.block_slashing_db_hist.Keys == s.block_slashing_db_hist.Keys + s'.active_consensus_instances_on_beacon_blocks.Keys;

    //     assert forall slot, vp: BeaconBlock -> bool |
    //                 && slot in s.block_slashing_db_hist.Keys
    //                 && vp in s.block_slashing_db_hist[slot].Keys
    //                 ::
    //                 && s.block_slashing_db_hist.Keys <= s'.block_slashing_db_hist.Keys
    //                 && s.block_slashing_db_hist[slot].Keys <= s'.block_slashing_db_hist[slot].Keys
    //                 && s.block_slashing_db_hist[slot][vp] <= s'.block_slashing_db_hist[slot][vp]
    //     ;

    //     assert forall slot |
    //                 && slot in s'.active_consensus_instances_on_beacon_blocks.Keys
    //                 && slot in s.block_slashing_db_hist.Keys
    //                 && var vp := s'.active_consensus_instances_on_beacon_blocks[slot].validityPredicate;
    //                 && vp in s.block_slashing_db_hist[slot].Keys
    //                 ::
    //                 var vp := s'.active_consensus_instances_on_beacon_blocks[slot].validityPredicate;
    //                 s.block_slashing_db_hist[slot][vp] + {new_block_slashing_db} == s'.block_slashing_db_hist[slot][vp];

    //     assert forall slot, vp: BeaconBlock -> bool |
    //                 && slot in s'.block_slashing_db_hist.Keys
    //                 && slot !in s.block_slashing_db_hist.Keys
    //                 && vp in s'.block_slashing_db_hist[slot].Keys
    //                 ::
    //                 && vp == s'.active_consensus_instances_on_beacon_blocks[slot].validityPredicate
    //     ;

    //     assert forall slot, vp: BeaconBlock -> bool |
    //                 && slot in s.block_slashing_db_hist.Keys
    //                 && vp in s'.block_slashing_db_hist[slot].Keys
    //                 && vp !in s.block_slashing_db_hist[slot].Keys
    //                 ::
    //                 && s'.block_slashing_db_hist[slot][vp] == {new_block_slashing_db}
    //     ;

    // }

    // lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_duty_updateBlockConsensusInstanceValidityCheck2(
    //     s: BlockConsensusEngineState,
    //     new_block_slashing_db: set<SlashingDBBlock>,
    //     s': BlockConsensusEngineState,
    //     slot: Slot,
    //     vp: BeaconBlock -> bool
    // )
    // requires s' == updateBlockConsensusInstanceValidityCheck(s, new_block_slashing_db)
    // requires
    //                 && slot in s'.active_consensus_instances_on_beacon_blocks.Keys
    //                 && slot in s.block_slashing_db_hist.Keys
    //                 && vp == s'.active_consensus_instances_on_beacon_blocks[slot].validityPredicate
    //                 && vp in s.block_slashing_db_hist[slot].Keys
    // ensures s.block_slashing_db_hist[slot][vp] + {new_block_slashing_db} == s'.block_slashing_db_hist[slot][vp];
    // {
    //     lem_updateBlockConsensusInstanceValidityCheckHelper(s.active_consensus_instances_on_beacon_blocks, new_block_slashing_db, s'.active_consensus_instances_on_beacon_blocks);

    //     assert s'.block_slashing_db_hist.Keys == s.block_slashing_db_hist.Keys + s'.active_consensus_instances_on_beacon_blocks.Keys;
    // }

    // lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_duty_updateBlockConsensusInstanceValidityCheck3(
    //     s: BlockConsensusEngineState,
    //     new_block_slashing_db: set<SlashingDBBlock>,
    //     s': BlockConsensusEngineState,
    //     slot: Slot,
    //     vp: BeaconBlock -> bool
    // )
    // requires s' == updateBlockConsensusInstanceValidityCheck(s, new_block_slashing_db)
    // requires
    //                 && slot in s'.active_consensus_instances_on_beacon_blocks.Keys
    //                 && slot in s.block_slashing_db_hist.Keys
    //                 && vp != s'.active_consensus_instances_on_beacon_blocks[slot].validityPredicate
    //                 && vp in s.block_slashing_db_hist[slot].Keys
    // ensures s.block_slashing_db_hist[slot][vp] == s'.block_slashing_db_hist[slot][vp];
    // {
    //     lem_updateBlockConsensusInstanceValidityCheckHelper(s.active_consensus_instances_on_beacon_blocks, new_block_slashing_db, s'.active_consensus_instances_on_beacon_blocks);

    //     assert s'.block_slashing_db_hist.Keys == s.block_slashing_db_hist.Keys + s'.active_consensus_instances_on_beacon_blocks.Keys;
    // }

    // lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_duty_updateBlockConsensusInstanceValidityCheck4(
    //     s: BlockConsensusEngineState,
    //     new_block_slashing_db: set<SlashingDBBlock>,
    //     s': BlockConsensusEngineState,
    //     slot: Slot,
    //     vp: BeaconBlock -> bool
    // )
    // requires s' == updateBlockConsensusInstanceValidityCheck(s, new_block_slashing_db)
    // requires
    //                 && slot !in s'.active_consensus_instances_on_beacon_blocks.Keys
    //                 && slot in s.block_slashing_db_hist.Keys
    //                 && vp in s.block_slashing_db_hist[slot].Keys
    // ensures s.block_slashing_db_hist[slot][vp] == s'.block_slashing_db_hist[slot][vp];
    // {
    //     lem_updateBlockConsensusInstanceValidityCheckHelper(s.active_consensus_instances_on_beacon_blocks, new_block_slashing_db, s'.active_consensus_instances_on_beacon_blocks);

    //     assert s'.block_slashing_db_hist.Keys == s.block_slashing_db_hist.Keys + s'.active_consensus_instances_on_beacon_blocks.Keys;
    // }

    // lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_duty_updateBlockConsensusInstanceValidityCheck5(
    //     s: BlockConsensusEngineState,
    //     new_block_slashing_db: set<SlashingDBBlock>,
    //     s': BlockConsensusEngineState,
    //     slot: Slot
    // )
    // requires s' == updateBlockConsensusInstanceValidityCheck(s, new_block_slashing_db)
    // requires slot in s.block_slashing_db_hist.Keys
    // ensures slot in s'.block_slashing_db_hist.Keys
    // ensures s.block_slashing_db_hist[slot].Keys <= s'.block_slashing_db_hist[slot].Keys;
    // {
    //     lem_updateBlockConsensusInstanceValidityCheckHelper(s.active_consensus_instances_on_beacon_blocks, new_block_slashing_db, s'.active_consensus_instances_on_beacon_blocks);

    //     assert s'.block_slashing_db_hist.Keys == s.block_slashing_db_hist.Keys + s'.active_consensus_instances_on_beacon_blocks.Keys;
    // }

    // lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2_f_terminate_current_proposer_duty(
    //     process: DVCState,
    //     process': DVCState
    // )
    // requires f_terminate_current_proposer_duty.requires(process)
    // requires process' == f_terminate_current_proposer_duty(process)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2(process)
    // ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2(process')
    // { }

    // // TODO: new proof
    // lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_check_for_next_duty_helper(
    //     process: DVCState,
    //     proposer_duty: ProposerDuty,
    //     s': DVCState
    // )
    // requires f_check_for_next_duty.requires(process, proposer_duty)
    // requires s' == f_check_for_next_duty(process, proposer_duty).state
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2(process)
    // // ensures  inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2(s')
    // {
    //     var block_slashing_db := process.block_slashing_db;

    //     var acvc := BlockConsensusValidityCheckState(
    //         proposer_duty := proposer_duty,
    //         validityPredicate := (ad: BeaconBlock) => ci_decision_is_valid_beacon_block(block_slashing_db, ad, proposer_duty)
    //     );

    //     // assert s'.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks == process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[proposer_duty.slot := acvc];


    //     forall cid | cid in s'.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks
    //         // ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2_body(s', cid);
    //     {
    //         if cid != proposer_duty.slot
    //         {
    //             assert cid in process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks;
    //             // assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2_body(s', cid);
    //         }
    //         else
    //         {
    //             assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(
    //                 cid,
    //                 proposer_duty,
    //                 block_slashing_db,
    //                 acvc.validityPredicate
    //             );
    //             assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2_body(s', cid);
    //         }
    //     }
    // }

    // lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_start_next_duty(
    //     process: DVCState,
    //     proposer_duty: ProposerDuty,
    //     process': DVCState
    // )
    // requires f_check_for_next_duty.requires(process, proposer_duty)
    // requires process' == f_start_next_duty(process, proposer_duty).state
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2(process)
    // ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2(process')
    // {
    //     var new_process := f_new_process_after_starting_new_proposer_duty(process, proposer_duty);

    //     assert { proposer_duty.slot } ==
    //                  new_process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys -
    //                         process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys;

    //     forall cid | cid in new_process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks
    //     ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2_body(new_process, cid)
    //     {
    //         if cid in process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks
    //         {
    //             assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2_body(new_process, cid);
    //         }
    //         else
    //         {
    //             assert cid == proposer_duty.slot;

    //             var acvc := BlockConsensusValidityCheckState(
    //                 proposer_duty := proposer_duty,
    //                 validityPredicate := (ad: BeaconBlock) => ci_decision_is_valid_beacon_block(process.block_slashing_db, ad, proposer_duty)
    //             );

    //             assert acvc == process'.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid];
    //             assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(cid, proposer_duty, process.block_slashing_db, acvc.validityPredicate);
    //             assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2_body_body(cid, proposer_duty, acvc.validityPredicate);
    //             assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2_body(new_process, cid);
    //         }
    //     }
    // }

    // lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2_f_check_for_next_duty(
    //     process: DVCState,
    //     proposer_duty: ProposerDuty,
    //     process': DVCState
    // )
    // requires f_check_for_next_duty.requires(process, proposer_duty)
    // requires process' == f_check_for_next_duty(process, proposer_duty).state
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2(process)
    // ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2(process');
    // {
    //     if pred_decision_of_proposer_duty_was_known(process, proposer_duty)
    //     {
    //         var new_process := f_new_process_after_updateBlockConsensusInstanceValidityCheck(process, proposer_duty);

    //         lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_updateBlockConsensusInstanceValidityCheckHelper(
    //                 process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks,
    //                 new_process.block_slashing_db,
    //                 new_process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks
    //         );
    //     }
    //     else
    //     {
    //         lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_start_next_duty(
    //             process,
    //             proposer_duty,
    //             process'
    //         );
    //     }
    // }

    // lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2_f_serve_proposer_duty(
    //     process: DVCState,
    //     proposer_duty: ProposerDuty,
    //     process': DVCState
    // )
    // requires f_serve_proposer_duty.requires(process, proposer_duty)
    // requires process' == f_serve_proposer_duty(process, proposer_duty).state
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2(process)
    // ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2(process');
    // {
    //     var process_rcvd_duty :=
    //             process.(all_rcvd_duties := process.all_rcvd_duties + {proposer_duty});
    //     var process_after_stopping_active_consensus_instance := f_terminate_current_proposer_duty(process_rcvd_duty);
    //     lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2_f_terminate_current_proposer_duty(
    //         process_rcvd_duty,
    //         process_after_stopping_active_consensus_instance
    //     );
    //     lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2_f_check_for_next_duty(
    //         process_after_stopping_active_consensus_instance,
    //         proposer_duty,
    //         process'
    //     );
    // }

    // lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2_f_block_consensus_decided(
    //     process: DVCState,
    //     id: Slot,
    //     decided_beacon_block: BeaconBlock,
    //     s': DVCState
    // )
    // requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    // requires s' == f_block_consensus_decided(process, id, decided_beacon_block).state
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2(process)
    // ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2(s');
    // {
    //     if  is_decided_data_for_current_slot(process, decided_beacon_block, id)
    //     {
    //         var s_mod := f_update_process_after_proposer_duty_decided(
    //                         process,
    //                         id,
    //                         decided_beacon_block);

    //         lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_updateBlockConsensusInstanceValidityCheckHelper(
    //                 process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks,
    //                 s_mod.block_slashing_db,
    //                 s_mod.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks
    //         );
    //     }
    // }

    // lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_f_listen_for_new_imported_blocks(
    //     process: DVCState,
    //     block: BeaconBlock,
    //     s': DVCState
    // )
    // requires f_listen_for_new_imported_blocks.requires(process, block)
    // requires s' == f_listen_for_new_imported_blocks(process, block).state
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2(process)
    // ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2(s');
    // {
    //     var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

    //     var proposer_consensus_instances_already_decided := process.future_proposer_consensus_instances_already_decided + new_consensus_instances_already_decided;

    //     var process := f_stopBlockConsensusInstances_after_receiving_new_imported_blocks(
    //                             process,
    //                             block
    //                         );

    //     if pred_listen_for_new_imported_blocks_checker(process, proposer_consensus_instances_already_decided)
    //     {
    //         var s_mod := f_updateBlockConsensusInstanceValidityCheck_in_listen_for_new_imported_blocks(
    //                                 process,
    //                                 proposer_consensus_instances_already_decided
    //                             );

    //         lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_updateBlockConsensusInstanceValidityCheckHelper(
    //                 process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks,
    //                 s_mod.block_slashing_db,
    //                 s_mod.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks
    //         );
    //     }
    // }

    // lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv_next_ServeProposerDuty(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires event.HonestNodeTakingStep?
    // requires event.event.ServeProposerDuty?
    // requires inv_quorum_constraints(s)
    // requires inv_unchanged_paras_of_consensus_instances(s)
    // requires inv_only_dv_construct_complete_signed_block(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    // ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s')
    // {
    //     match event
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             var s_node := s.honest_nodes_states[node];
    //             var s'_node := s'.honest_nodes_states[node];
    //             match nodeEvent
    //             {
    //                 case ServeProposerDuty(proposer_duty) =>
    //                     forall n | n in s'.honest_nodes_states
    //                     ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2(s'.honest_nodes_states[n]);
    //                     {
    //                         if n == node
    //                         {
    //                             lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2_f_serve_proposer_duty(s_node, proposer_duty, s'_node);
    //                             assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2(s'_node);
    //                         }
    //                     }
    //                     assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s');
    //             }
    //     }
    // }

    // lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv_next_BlockConsensusDecided(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires event.HonestNodeTakingStep?
    // requires event.event.BlockConsensusDecided?
    // requires inv_quorum_constraints(s)
    // requires inv_unchanged_paras_of_consensus_instances(s)
    // requires inv_only_dv_construct_complete_signed_block(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    // ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s')
    // {
    //     match event
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             var s_node := s.honest_nodes_states[node];
    //             var s'_node := s'.honest_nodes_states[node];
    //             match nodeEvent
    //             {
    //                 case BlockConsensusDecided(id, decided_beacon_block) =>
    //                     forall n | n in s'.honest_nodes_states
    //                     ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2(s'.honest_nodes_states[n]);
    //                     {
    //                         if n == node
    //                         {
    //                             lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2_f_block_consensus_decided(s_node, id, decided_beacon_block, s'_node);
    //                             assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2(s'_node);
    //                         }
    //                     }
    //                     assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s');
    //             }
    //     }
    // }

    // lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv_next_ReceivedSignedBeaconBlock(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires event.HonestNodeTakingStep?
    // requires event.event.ReceivedSignedBeaconBlock?
    // requires inv_quorum_constraints(s)
    // requires inv_unchanged_paras_of_consensus_instances(s)
    // requires inv_only_dv_construct_complete_signed_block(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    // ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s')
    // {
    //     match event
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             var s_node := s.honest_nodes_states[node];
    //             var s'_node := s'.honest_nodes_states[node];
    //             match nodeEvent
    //             {
    //                 case ReceivedSignedBeaconBlock(block_share) =>
    //                     forall n | n in s'.honest_nodes_states
    //                     ensures s'.honest_nodes_states[n].block_consensus_engine_state == s.honest_nodes_states[n].block_consensus_engine_state
    //                     {
    //                         if n == node
    //                         {
    //                             lem_f_listen_for_block_signature_shares_unchanged_dvc_vars(s_node, block_share, s'_node);
    //                         }
    //                     }
    //                     assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s');
    //             }
    //     }
    // }

    // lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv_next_ImportedNewBlock(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires event.HonestNodeTakingStep?
    // requires event.event.ImportedNewBlock?
    // requires inv_quorum_constraints(s)
    // requires inv_unchanged_paras_of_consensus_instances(s)
    // requires inv_only_dv_construct_complete_signed_block(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    // ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s')
    // {
    //     match event
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             var s_node := s.honest_nodes_states[node];
    //             var s'_node := s'.honest_nodes_states[node];
    //             match nodeEvent
    //             {
    //                 case ImportedNewBlock(block) =>
    //                     forall n | n in s'.honest_nodes_states
    //                     ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2(s'.honest_nodes_states[n]);
    //                     {
    //                         if n == node
    //                         {
    //                             var s_node := f_add_block_to_bn(s_node, nodeEvent.block);
    //                             lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_f_listen_for_new_imported_blocks(s_node, block, s'_node);
    //                             assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc_2(s'_node);
    //                         }
    //                     }
    //                     assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s');
    //             }
    //     }
    // }

    // lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv_next(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires inv_quorum_constraints(s)
    // requires inv_unchanged_paras_of_consensus_instances(s)
    // requires inv_only_dv_construct_complete_signed_block(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    // ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s')
    // {
    //     match event
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             var s_node := s.honest_nodes_states[node];
    //             var s'_node := s'.honest_nodes_states[node];
    //             match nodeEvent
    //             {
    //                 case ServeProposerDuty(proposer_duty) =>
    //                     lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv_next_ServeProposerDuty(
    //                         s,
    //                         event,
    //                         s'
    //                     );

    //                 case BlockConsensusDecided(id, decided_beacon_block) =>
    //                     lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv_next_BlockConsensusDecided(
    //                         s,
    //                         event,
    //                         s'
    //                     );


    //                 case ReceivedSignedBeaconBlock(block_share) =>
    //                     lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv_next_ReceivedSignedBeaconBlock(
    //                         s,
    //                         event,
    //                         s'
    //                     );

    //                 case ImportedNewBlock(block) =>
    //                     lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv_next_ImportedNewBlock(
    //                         s,
    //                         event,
    //                         s'
    //                     );

    //                 case ResendSignedBeaconBlocks =>
    //                     assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s');

    //                 case NoEvent =>
    //                     assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s');
    //             }

    //         case AdversaryTakingStep(node, new_randao_shares_sent, new_block_shares_sent, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
    //             assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s');
    //     }
    // }

    // lemma lem_f_listen_for_new_imported_blocks_helper_1(
    //     dv: DVState,
    //     process: DVCState,
    //     block: BeaconBlock,
    //     new_consensus_instances_already_decided: map<Slot, BeaconBlock>
    // )
    // requires f_listen_for_new_imported_blocks_helper_1.requires(process, block)
    // requires new_consensus_instances_already_decided == f_listen_for_new_imported_blocks_helper_1(process, block)
    // requires inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(dv)
    // requires inv_block_of_block_share_is_decided_value(dv)
    // requires pred_axiom_is_my_proposer_2(dv, process, block)
    // ensures forall slot |
    //             slot in new_consensus_instances_already_decided
    //             ::
    //             && dv.consensus_instances_on_beacon_block[slot].decided_value.isPresent()
    //             && dv.consensus_instances_on_beacon_block[slot].decided_value.safe_get() == new_consensus_instances_already_decided[slot]
    //             ;
    // {
    //     forall slot | slot in new_consensus_instances_already_decided
    //     ensures
    //         && dv.consensus_instances_on_beacon_block[slot].decided_value.isPresent()
    //         && dv.consensus_instances_on_beacon_block[slot].decided_value.safe_get() == new_consensus_instances_already_decided[slot]
    //         ;
    //     {

    //         var valIndex := bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);


    //         var a :|
    //             && a in block.body.proposers
    //             && DVC_Spec_NonInstr.isMyAttestation(a, process.bn, block, valIndex)
    //             && a.data == new_consensus_instances_already_decided[slot]
    //         ;

    //         var a' :|
    //             && a' in dv.all_blocks_created
    //             && a'.data == a.data
    //             && is_valid_proposer(a', dv.dv_pubkey);

    //         var hn', block_share: SignedBeaconBlock :| inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(dv, hn', block_share, a');

    //         assert
    //         && dv.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.isPresent()
    //         && dv.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.safe_get() == block_share.block;

    //         assert
    //         && dv.consensus_instances_on_beacon_block[slot].decided_value.isPresent()
    //         && dv.consensus_instances_on_beacon_block[slot].decided_value.safe_get() == new_consensus_instances_already_decided[slot]
    //         ;
    //     }
    // }

    // lemma lem_inv_sequence_proposer_duties_to_be_served_ordered_dv_next(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires inv_sequence_proposer_duties_to_be_served_ordered(s)
    // ensures inv_sequence_proposer_duties_to_be_served_ordered(s')
    // {
    //     match event
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             assert s'.sequence_proposer_duties_to_be_served == s.sequence_proposer_duties_to_be_served;

    //         case AdversaryTakingStep(node, new_randao_shares_sent, new_block_shares_sent, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
    //             assert s'.sequence_proposer_duties_to_be_served == s.sequence_proposer_duties_to_be_served;
    //     }
    //     assert s'.sequence_proposer_duties_to_be_served == s.sequence_proposer_duties_to_be_served;

    // }

    // // TODO: Simplify
    // lemma lem_inv_block_of_block_share_is_decided_value_proposer_consensus_decided_helper_1(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState,
    //     hn: BLSPubkey,
    //     block_share: SignedBeaconBlock
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires event.HonestNodeTakingStep?
    // requires event.event.BlockConsensusDecided?
    // requires inv_block_of_block_share_is_decided_value(s)
    // requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    // requires inv_block_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)
    // requires inv_quorum_constraints(s)
    // requires inv_unchanged_paras_of_consensus_instances(s)
    // requires same_honest_nodes_in_dv_and_ci(s)
    // requires inv_only_dv_construct_complete_signed_block(s)
    // requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    // requires |s.all_nodes| > 0
    // requires is_correct_block_share(s, hn, block_share)
    // requires block_share in s.block_share_network.allMessagesSent
    // ensures && s'.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.isPresent()
    //         && s'.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.safe_get() == block_share.block
    // {
    //     match event
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             var s_node := s.honest_nodes_states[node];
    //             var s'_node := s'.honest_nodes_states[node];
    //             match nodeEvent
    //             {
    //                 case BlockConsensusDecided(id: Slot, decided_beacon_block) =>
    //                     assert block_share in s.block_share_network.allMessagesSent;
    //                     assert inv_block_of_block_share_is_decided_value(s);
    //                     assert inv_block_of_block_share_is_decided_value_body(s, block_share);
    //                     assert s.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.isPresent();
    //                     assert s.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.safe_get() == block_share.block;

    //                     var s_w_honest_node_states_updated := lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_get_s_w_honest_node_states_updated(s, node, nodeEvent);
    //                     var cid := block_share.block.slot;

    //                     assert s_w_honest_node_states_updated.consensus_instances_on_beacon_block == s.consensus_instances_on_beacon_block;

    //                     var output :=
    //                         if nodeEvent.BlockConsensusDecided? && nodeEvent.id == cid then
    //                             Some(Decided(node, nodeEvent.decided_beacon_block))
    //                         else
    //                             None
    //                         ;

    //                     var validityPredicates :=
    //                         map n |
    //                                 && n in s_w_honest_node_states_updated.honest_nodes_states.Keys
    //                                 && cid in s_w_honest_node_states_updated.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys
    //                             ::
    //                                 s_w_honest_node_states_updated.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid].validityPredicate
    //                         ;

    //                     var s_consensus := s_w_honest_node_states_updated.consensus_instances_on_beacon_block[cid];
    //                     var s'_consensus := s'.consensus_instances_on_beacon_block[cid];

    //                     assert
    //                         Block_Consensus_Spec.Next(
    //                             s_consensus,
    //                             validityPredicates,
    //                             s'_consensus,
    //                             output
    //                         );

    //                     lem_consensus_next_under_safety(
    //                         s_consensus,
    //                         validityPredicates,
    //                         s'_consensus,
    //                         output
    //                     );

    //                     assert s'.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.isPresent();
    //                     assert s.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.safe_get() == s'.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.safe_get();
    //                         assert s'.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.safe_get() == block_share.block;
    //             }
    //     }
    // }

    // // // Ver time: 1m 35s
    // // IMPORTANT: Seem to be an error of Dafny with the second match expression
    // // lemma lem_inv_block_of_block_share_is_decided_value_dv_next(
    // //     s: DVState,
    // //     event: DV_Block_Proposer_Spec.Event,
    // //     s': DVState
    // // )
    // // requires NextEventPreCond(s, event)
    // // requires NextEvent(s, event, s')
    // // requires inv_quorum_constraints(s)
    // // requires inv_unchanged_paras_of_consensus_instances(s)
    // // requires same_honest_nodes_in_dv_and_ci(s)
    // // requires inv_only_dv_construct_complete_signed_block(s)
    // // requires inv_block_of_block_share_is_decided_value(s)
    // // requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    // // requires inv_block_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)
    // // requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)
    // // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    // // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    // // requires |s.all_nodes| > 0
    // // // ensures inv_block_of_block_share_is_decided_value(s')
    // // {
    // //     match event
    // //     {
    // //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    // //             var s_node := s.honest_nodes_states[node];
    // //             var s'_node := s'.honest_nodes_states[node];
    // //             if nodeEvent.BlockConsensusDecided?
    // //             {
    // //                 // lem_inv_block_of_block_share_is_decided_value_proposer_consensus_decided(s, event, s');
    // //             }
    // //             else
    // //             {
    // //                 match nodeEvent
    // //                 {
    // //                     // case ServeProposerDuty(proposer_duty) =>
    // //                     //     var messagesToBeSent := f_serve_proposer_duty(s_node, proposer_duty).outputs.block_shares_sent;
    // //                     //     assert s'.block_share_network.allMessagesSent == s.block_share_network.allMessagesSent +
    // //                     //         getMessagesFromMessagesWithRecipient(messagesToBeSent);
    // //                     //     lem_f_serve_proposer_duty_unchanged_vars(s_node, proposer_duty, s'_node);
    // //                     //     assert messagesToBeSent == {};
    // //                     //     lem_inv_block_of_block_share_is_decided_value_helper2(s'.block_share_network.allMessagesSent, s.block_share_network.allMessagesSent, messagesToBeSent);
    // //                     //     assert s'.block_share_network.allMessagesSent == s.block_share_network.allMessagesSent;


    // //                     // case ReceivedSignedBeaconBlock(block_share) =>
    // //                     //     var messagesToBeSent := f_listen_for_block_signature_shares(s_node, block_share).outputs.block_shares_sent;
    // //                     //     assert messagesToBeSent == {};
    // //                     //     assert s'.block_share_network.allMessagesSent ==
    // //                     //                 s.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent);
    // //                     //     assert s'.block_share_network.allMessagesSent ==
    // //                     //                 s.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient({});

    // //                     // case ImportedNewBlock(block) =>
    // //                     //     var s_node := f_add_block_to_bn(s_node, nodeEvent.block);
    // //                     //     var messagesToBeSent := f_listen_for_new_imported_blocks(s_node, block).outputs.block_shares_sent;
    // //                     //     assert s'.block_share_network.allMessagesSent ==
    // //                     //                 s.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent);
    // //                     //     lem_f_listen_for_new_imported_blocks_unchanged_dvc_vars(s_node, block, s'_node);
    // //                     //     assert messagesToBeSent == {};
    // //                     //     lem_inv_block_of_block_share_is_decided_value_helper2(s'.block_share_network.allMessagesSent, s.block_share_network.allMessagesSent, messagesToBeSent);
    // //                     //     assert s'.block_share_network.allMessagesSent == s.block_share_network.allMessagesSent;

    // //                     // case ResendSignedBeaconBlocks =>
    // //                     //     var messagesToBeSent := f_resend_block_share(s_node).outputs.block_shares_sent;

    // //                     //     assert s'.block_share_network.allMessagesSent ==
    // //                     //                 s.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent);

    // //                     //     forall m | m in getMessagesFromMessagesWithRecipient(messagesToBeSent)
    // //                     //     ensures m in s.block_share_network.allMessagesSent
    // //                     //     {
    // //                     //         assert m in s_node.block_shares_to_broadcast.Values;
    // //                     //         assert m in s.block_share_network.allMessagesSent;
    // //                     //     }

    // //                     //     assert s'.block_share_network.allMessagesSent == s.block_share_network.allMessagesSent;

    // //                     // case NoEvent =>
    // //                     //     assert s'.block_share_network == s.block_share_network;
    // //                 }
    // //                 // lem_inv_block_of_block_share_is_decided_value_helper(s, event, s');
    // //             }


    // //         case AdversaryTakingStep(node, new_randao_shares_sent, new_block_shares_sent, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
    // //         //     lem_inv_block_of_block_share_is_decided_value_proposer_adversary(s, event, s');
    // //     }
    // // }

    // lemma lem_inv_block_of_block_share_is_decided_value_dv_next_ServeProposerDuty(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires event.HonestNodeTakingStep?
    // requires event.event.ServeProposerDuty?
    // requires inv_quorum_constraints(s)
    // requires inv_unchanged_paras_of_consensus_instances(s)
    // requires same_honest_nodes_in_dv_and_ci(s)
    // requires inv_only_dv_construct_complete_signed_block(s)
    // requires inv_block_of_block_share_is_decided_value(s)
    // requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    // requires inv_block_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)
    // requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    // requires |s.all_nodes| > 0
    // ensures inv_block_of_block_share_is_decided_value(s')
    // {
    //     match event
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             var s_node := s.honest_nodes_states[node];
    //             var s'_node := s'.honest_nodes_states[node];
    //             match nodeEvent
    //             {
    //                 case ServeProposerDuty(proposer_duty) =>
    //                     var messagesToBeSent := f_serve_proposer_duty(s_node, proposer_duty).outputs.block_shares_sent;
    //                     assert s'.block_share_network.allMessagesSent ==
    //                                 s.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent);
    //                     lem_f_serve_proposer_duty_unchanged_vars(s_node, proposer_duty, s'_node);
    //                     assert messagesToBeSent == {};
    //                     lem_inv_block_of_block_share_is_decided_value_helper2(s'.block_share_network.allMessagesSent, s.block_share_network.allMessagesSent, messagesToBeSent);
    //                     assert s'.block_share_network.allMessagesSent == s.block_share_network.allMessagesSent;
    //                     lem_inv_block_of_block_share_is_decided_value_helper(s, event, s');
    //             }
    //     }
    // }

    // lemma lem_inv_block_of_block_share_is_decided_value_dv_next_ReceivedSignedBeaconBlock(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires event.HonestNodeTakingStep?
    // requires event.event.ReceivedSignedBeaconBlock?
    // requires inv_quorum_constraints(s)
    // requires inv_unchanged_paras_of_consensus_instances(s)
    // requires same_honest_nodes_in_dv_and_ci(s)
    // requires inv_only_dv_construct_complete_signed_block(s)
    // requires inv_block_of_block_share_is_decided_value(s)
    // requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    // requires inv_block_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)
    // requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    // requires |s.all_nodes| > 0
    // ensures inv_block_of_block_share_is_decided_value(s')
    // {
    //     match event
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             var s_node := s.honest_nodes_states[node];
    //             var s'_node := s'.honest_nodes_states[node];
    //             match nodeEvent
    //             {
    //                 case ReceivedSignedBeaconBlock(block_share) =>
    //                     var messagesToBeSent := f_listen_for_block_signature_shares(s_node, block_share).outputs.block_shares_sent;
    //                         assert messagesToBeSent == {};
    //                         assert s'.block_share_network.allMessagesSent ==
    //                                     s.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent);
    //                         assert s'.block_share_network.allMessagesSent ==
    //                                     s.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient({});
    //                     lem_inv_block_of_block_share_is_decided_value_helper(s, event, s');
    //             }
    //     }
    // }

    // lemma lem_inv_block_of_block_share_is_decided_value_dv_next_ImportedNewBlock(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires event.HonestNodeTakingStep?
    // requires event.event.ImportedNewBlock?
    // requires inv_quorum_constraints(s)
    // requires inv_unchanged_paras_of_consensus_instances(s)
    // requires same_honest_nodes_in_dv_and_ci(s)
    // requires inv_only_dv_construct_complete_signed_block(s)
    // requires inv_block_of_block_share_is_decided_value(s)
    // requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    // requires inv_block_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)
    // requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    // requires |s.all_nodes| > 0
    // ensures inv_block_of_block_share_is_decided_value(s')
    // {
    //     match event
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             var s_node := s.honest_nodes_states[node];
    //             var s'_node := s'.honest_nodes_states[node];
    //             match nodeEvent
    //             {
    //                 case ImportedNewBlock(block) =>
    //                     var s_node := f_add_block_to_bn(s_node, nodeEvent.block);
    //                         var messagesToBeSent := f_listen_for_new_imported_blocks(s_node, block).outputs.block_shares_sent;
    //                         assert s'.block_share_network.allMessagesSent ==
    //                                     s.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent);
    //                         lem_f_listen_for_new_imported_blocks_unchanged_dvc_vars(s_node, block, s'_node);
    //                         assert messagesToBeSent == {};
    //                         lem_inv_block_of_block_share_is_decided_value_helper2(s'.block_share_network.allMessagesSent, s.block_share_network.allMessagesSent, messagesToBeSent);
    //                         assert s'.block_share_network.allMessagesSent == s.block_share_network.allMessagesSent;
    //                     lem_inv_block_of_block_share_is_decided_value_helper(s, event, s');
    //             }
    //     }
    // }

    // lemma lem_inv_block_of_block_share_is_decided_value_dv_next_ResendSignedBeaconBlocks(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires event.HonestNodeTakingStep?
    // requires event.event.ResendSignedBeaconBlocks?
    // requires inv_quorum_constraints(s)
    // requires inv_unchanged_paras_of_consensus_instances(s)
    // requires same_honest_nodes_in_dv_and_ci(s)
    // requires inv_only_dv_construct_complete_signed_block(s)
    // requires inv_block_of_block_share_is_decided_value(s)
    // requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    // requires inv_block_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)
    // requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    // requires |s.all_nodes| > 0
    // ensures inv_block_of_block_share_is_decided_value(s')
    // {
    //     match event
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             var s_node := s.honest_nodes_states[node];
    //             var s'_node := s'.honest_nodes_states[node];
    //             match nodeEvent
    //             {
    //                 case ResendSignedBeaconBlocks =>
    //                     var messagesToBeSent := f_resend_block_share(s_node).outputs.block_shares_sent;

    //                         assert s'.block_share_network.allMessagesSent ==
    //                                     s.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent);

    //                         forall m | m in getMessagesFromMessagesWithRecipient(messagesToBeSent)
    //                         ensures m in s.block_share_network.allMessagesSent
    //                         {
    //                             assert m in s_node.block_shares_to_broadcast.Values;
    //                             assert m in s.block_share_network.allMessagesSent;
    //                         }

    //                         assert s'.block_share_network.allMessagesSent == s.block_share_network.allMessagesSent;lem_inv_block_of_block_share_is_decided_value_helper(s, event, s');
    //             }
    //     }
    // }

    // lemma lem_inv_block_of_block_share_is_decided_value_dv_next(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')
    // requires inv_quorum_constraints(s)
    // requires inv_unchanged_paras_of_consensus_instances(s)
    // requires same_honest_nodes_in_dv_and_ci(s)
    // requires inv_only_dv_construct_complete_functions(s)
    // requires inv_block_of_block_share_is_decided_value(s)
    // requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    // requires inv_block_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)
    // requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    // requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    // requires |s.all_nodes| > 0
    // ensures inv_block_of_block_share_is_decided_value(s')
    // {
    //     assert inv_only_dv_construct_complete_signed_block(s);
    //     match event
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             var s_node := s.honest_nodes_states[node];
    //             var s'_node := s'.honest_nodes_states[node];
    //             if nodeEvent.BlockConsensusDecided?
    //             {
    //                 lem_inv_block_of_block_share_is_decided_value_proposer_consensus_decided(s, event, s');
    //             }
    //             else
    //             {
    //                 match nodeEvent
    //                 {
    //                     case ServeProposerDuty(proposer_duty) =>
    //                         lem_inv_block_of_block_share_is_decided_value_dv_next_ServeProposerDuty(
    //                             s,
    //                             event,
    //                             s'
    //                         );


    //                     case ReceivedSignedBeaconBlock(block_share) =>
    //                         lem_inv_block_of_block_share_is_decided_value_dv_next_ReceivedSignedBeaconBlock(
    //                             s,
    //                             event,
    //                             s'
    //                         );

    //                     case ImportedNewBlock(block) =>
    //                         lem_inv_block_of_block_share_is_decided_value_dv_next_ImportedNewBlock(
    //                             s,
    //                             event,
    //                             s'
    //                         );

    //                     case ResendSignedBeaconBlocks =>
    //                         lem_inv_block_of_block_share_is_decided_value_dv_next_ResendSignedBeaconBlocks(
    //                             s,
    //                             event,
    //                             s'
    //                         );

    //                     case NoEvent =>
    //                         assert s'.block_share_network == s.block_share_network;
    //                         lem_inv_block_of_block_share_is_decided_value_helper(s, event, s');
    //                 }

    //             }

    //         case AdversaryTakingStep(node, new_randao_shares_sent, new_block_shares_sent, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
    //             lem_inv_block_of_block_share_is_decided_value_proposer_adversary(s, event, s');
    //     }
    // }


}