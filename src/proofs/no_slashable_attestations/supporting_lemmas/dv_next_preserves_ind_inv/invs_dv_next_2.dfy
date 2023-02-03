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
include "../inv.dfy"
include "../../../common/helper_pred_fcn.dfy"


module Invs_DV_Next_2
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Spec
    import opened DV    
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Helper_Sets_Lemmas
    import opened Common_Proofs
    import opened Invs_DV_Next_1
    import DVC_Spec_NonInstr
    import opened DVC_Spec_Axioms
    import opened Helper_Pred_Fcn

    predicate pred_the_latest_attestation_duty_was_sent_from_dv(
        s': DVState,
        index_next_attestation_duty_to_be_served: nat,
        attestation_duty: AttestationDuty,
        node: BLSPubkey
    )
    {
        && index_next_attestation_duty_to_be_served > 0
        && var an := s'.sequence_attestation_duties_to_be_served[index_next_attestation_duty_to_be_served - 1];
        && attestation_duty == an.attestation_duty
        && node == an.node    
    }    

    lemma lem_ServeAttstationDuty2_helper(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Types.Event,
        nodeOutputs: DVC_Spec.Outputs,
        s': DVState
    )
    requires NextHonestAfterAddingBlockToBn.requires(s, node, nodeEvent, nodeOutputs, s' );
    requires NextHonestAfterAddingBlockToBn(s, node, nodeEvent, nodeOutputs, s' );  
    requires nodeEvent.ServeAttstationDuty?
    ensures s'.index_next_attestation_duty_to_be_served > 0
    ensures && pred_the_latest_attestation_duty_was_sent_from_dv(s', s'.index_next_attestation_duty_to_be_served, nodeEvent.attestation_duty, node )
            && s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
    {

        var s_node := s.honest_nodes_states[node];
        var s'_node := s'.honest_nodes_states[node];
        assert  NextHonestAfterAddingBlockToBn.requires(add_block_to_bn_with_event(s, node, nodeEvent), node, nodeEvent, nodeOutputs, s' );
        assert  NextHonestAfterAddingBlockToBn(add_block_to_bn_with_event(s, node, nodeEvent), node, nodeEvent, nodeOutputs, s' );

        match nodeEvent
        {
            case ServeAttstationDuty(attestation_duty) => 
                assert s.sequence_attestation_duties_to_be_served == s'.sequence_attestation_duties_to_be_served;
                assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;

                var an := s'.sequence_attestation_duties_to_be_served[s'.index_next_attestation_duty_to_be_served - 1];

                assert attestation_duty == an.attestation_duty;
                assert node == an.node;
        }
    }     

    // // TODO: Rename to lem_ServeAttstationDuty
    lemma lem_ServeAttstationDuty(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')    
    requires event.HonestNodeTakingStep?
    requires event.event.ServeAttstationDuty?
    ensures s'.index_next_attestation_duty_to_be_served > 0
    ensures && pred_the_latest_attestation_duty_was_sent_from_dv(s', s'.index_next_attestation_duty_to_be_served, event.event.attestation_duty, event.node )
            && s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                assert  NextHonestAfterAddingBlockToBn.requires(add_block_to_bn_with_event(s, node, nodeEvent), node, nodeEvent, nodeOutputs, s' );
                assert  NextHonestAfterAddingBlockToBn(add_block_to_bn_with_event(s, node, nodeEvent), node, nodeEvent, nodeOutputs, s' );
                lem_ServeAttstationDuty2_helper(add_block_to_bn_with_event(s, node, nodeEvent), node, nodeEvent, nodeOutputs, s' );
        }        
    }    

    lemma lem_f_serve_attestation_duty_constants(
        s: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState
    )  
    requires f_serve_attestation_duty.requires(s, attestation_duty)
    requires s' == f_serve_attestation_duty(s, attestation_duty).state
    ensures s'.bn.attestations_submitted == s.bn.attestations_submitted      
    ensures s'.rcvd_attestation_shares == s.rcvd_attestation_shares
    ensures f_serve_attestation_duty(s, attestation_duty).outputs == getEmptyOuputs()
    { }

    lemma lem_f_check_for_next_duty_unchanged_dvc_vars(
        s: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState
    )
    requires f_check_for_next_duty.requires(s, attestation_duty)
    requires s' == f_check_for_next_duty(s, attestation_duty).state
    ensures s'.bn.attestations_submitted == s.bn.attestations_submitted
    ensures s'.rcvd_attestation_shares == s.rcvd_attestation_shares
    ensures f_check_for_next_duty(s, attestation_duty).outputs == getEmptyOuputs()
    { }

    lemma lem_f_att_consensus_decided_unchanged_dvc_vars(
        s: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCState
    )
    requires f_att_consensus_decided.requires(s, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(s, id, decided_attestation_data).state
    ensures s'.bn.attestations_submitted == s.bn.attestations_submitted
    ensures s'.rcvd_attestation_shares == s.rcvd_attestation_shares
    { } 

    // // Note: Lemma's name should be revisited due to second postcondition
    lemma lem_f_listen_for_new_imported_blocksd_unchanged_dvc_vars(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(s, block)
    requires s' == f_listen_for_new_imported_blocks(s, block).state
    ensures s'.bn.attestations_submitted == s.bn.attestations_submitted
    ensures s'.rcvd_attestation_shares.Keys <= s.rcvd_attestation_shares.Keys
    ensures forall k | k in s'.rcvd_attestation_shares.Keys :: s'.rcvd_attestation_shares[k] == s.rcvd_attestation_shares[k]
    ensures f_listen_for_new_imported_blocks(s, block).outputs == getEmptyOuputs()
    { }  

    lemma lem_f_listen_for_attestation_shares_unchanged_dvc_vars(
        s: DVCState,
        attestation_share: AttestationShare,
        s': DVCState
    )
    requires f_listen_for_attestation_shares.requires(s, attestation_share)
    requires s' == f_listen_for_attestation_shares(s, attestation_share).state    
    ensures s'.attestation_consensus_engine_state == s.attestation_consensus_engine_state
    ensures s'.attestation_consensus_engine_state.att_slashing_db_hist == s.attestation_consensus_engine_state.att_slashing_db_hist
    ensures s'.latest_attestation_duty == s.latest_attestation_duty
    ensures s'.current_attestation_duty == s.current_attestation_duty
    ensures s'.attestation_slashing_db == s.attestation_slashing_db
    ensures s'.future_att_consensus_instances_already_decided == s.future_att_consensus_instances_already_decided
    { }

    lemma lem_f_resend_attestation_share_unchanged_dvc_vars(
        s: DVCState,
        s': DVCState
    )
    requires f_resend_attestation_share.requires(s)
    requires s' == f_resend_attestation_share(s).state    
    ensures s'.attestation_consensus_engine_state == s.attestation_consensus_engine_state
    ensures s'.attestation_consensus_engine_state.att_slashing_db_hist == s.attestation_consensus_engine_state.att_slashing_db_hist
    ensures s'.latest_attestation_duty == s.latest_attestation_duty
    ensures s'.current_attestation_duty == s.current_attestation_duty
    ensures s'.attestation_slashing_db == s.attestation_slashing_db
    ensures s'.future_att_consensus_instances_already_decided == s.future_att_consensus_instances_already_decided
    { }    

    function recover_bls_signature(
        r: Root,
        signature: BLSSignature
    ): BLSPubkey
    requires exists pubkey :: verify_bls_signature(r, signature, pubkey)
    {
        var pubkey :| verify_bls_signature(r, signature, pubkey);
        pubkey
    }

    lemma lem_recover_bls_signature()
    ensures forall r, s1, s2 |
                && recover_bls_signature.requires(r, s1)
                && recover_bls_signature.requires(r, s2)
                && recover_bls_signature(r, s1) == recover_bls_signature(r, s2)
            ::
                s1 == s2
    {
        lem_verify_bls_signature();
    }

    lemma lem_inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        s': DVCState,
        dv: DVState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires s' == f_listen_for_attestation_shares(process, attestation_share).state
    requires construct_signed_attestation_signature_assumptions_helper(
        process.construct_signed_attestation_signature,
        process.dv_pubkey,
        dv.all_nodes
    )
    requires inv_quorum_constraints(dv)
    requires attestation_share in dv.att_network.allMessagesSent
    requires inv_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(dv, process)
    requires ( forall a | a in process.bn.attestations_submitted :: exists hn', att_share: AttestationShare ::
                    inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(dv, hn', att_share, a)
             )
    ensures forall a | a in s'.bn.attestations_submitted :: exists hn', att_share: AttestationShare :: inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(dv, hn', att_share, a)
    // ensures s'.bn.attestations_submitted == s.bn.attestations_submitted     
    {
        var activate_att_consensus_intances := process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

        if pred_listen_for_attestation_shares_checker(
                process,
                attestation_share) 
        {
            var k := (attestation_share.data, attestation_share.aggregation_bits);
            var process := f_add_new_attestation_share(
                                    process,
                                    attestation_share
                                );

                        
            if process.construct_signed_attestation_signature(process.rcvd_attestation_shares[attestation_share.data.slot][k]).isPresent()
            {
                var aggregated_attestation := 
                        Attestation(
                            aggregation_bits := attestation_share.aggregation_bits,
                            data := attestation_share.data,
                            signature := process.construct_signed_attestation_signature(process.rcvd_attestation_shares[attestation_share.data.slot][k]).safe_get()
                        );

                var att_shares := process.rcvd_attestation_shares[attestation_share.data.slot][k];
                assert construct_signed_attestation_signature_assumptions_reverse(
                    process.construct_signed_attestation_signature,
                    process.dv_pubkey,
                    dv.all_nodes                    
                );

                assert process.construct_signed_attestation_signature(att_shares).isPresent();

                assert construct_signed_attestation_signature_assumptions_reverse(
                    process.construct_signed_attestation_signature,
                    process.dv_pubkey,
                    dv.all_nodes
                );

                var data: AttestationData :|
                    construct_signed_attestation_signature_assumptions_reverse_helper(
                        process.construct_signed_attestation_signature,
                        process.dv_pubkey,
                        dv.all_nodes,
                        att_shares,
                        data                
                    );

                assert inv_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(dv, process);
                assert att_shares <= dv.att_network.allMessagesSent;

                var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(data.target.epoch));
                var signing_root := compute_attestation_signing_root(data, fork_version);


                var signers := 
                set signer, att_share | 
                    && att_share in att_shares
                    && signer in dv.all_nodes
                    && verify_bls_signature(signing_root, att_share.signature, signer)
                ::
                    signer;

                assert signers <= dv.all_nodes;

                lemmaThereExistsAnHonestInQuorum(dv.all_nodes, dv.all_nodes - dv.honest_nodes_states.Keys, signers);

                var h_s :| h_s in dv.honest_nodes_states.Keys && h_s in signers;
                var h_s_att :| h_s_att in att_shares && verify_bls_signature(signing_root, h_s_att.signature, h_s);               

                assert 
                && h_s in dv.honest_nodes_states.Keys
                && h_s_att in dv.att_network.allMessagesSent
                && h_s_att.data == data
                && verify_bls_signature(signing_root, h_s_att.signature, h_s);

                assert 
                && h_s in dv.honest_nodes_states.Keys
                && h_s_att in dv.att_network.allMessagesSent
                && h_s_att.data == data
                && verify_bls_signature(signing_root, h_s_att.signature, h_s);

                assert inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(
                    dv,
                    h_s,
                    h_s_att,
                    aggregated_attestation
                );

                var state := f_add_new_submitted_attestation(process, aggregated_attestation);

                forall a | a in state.bn.attestations_submitted 
                {
                    assert exists hn', att_share: AttestationShare :: inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(dv, hn', att_share, a);
                }
                assert s' == state;
            }
        }   
    }

    // TODO: simplify this proof
    lemma lem_inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_ex_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,

        s': DVCState,
        dv: DVState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires s' == f_listen_for_attestation_shares(process, attestation_share).state
    requires construct_signed_attestation_signature_assumptions_helper(
        process.construct_signed_attestation_signature,
        process.dv_pubkey,
        dv.all_nodes
    )
    requires inv_quorum_constraints(dv)
    requires attestation_share in dv.att_network.allMessagesSent
    requires inv_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(dv, process)
    ensures forall a | a in f_listen_for_attestation_shares(process, attestation_share).outputs.attestations_submitted ::
                        exists hn', att_share: AttestationShare :: inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(dv, hn', att_share, a);
    {
        var activate_att_consensus_intances := process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

        if pred_listen_for_attestation_shares_checker(
                process,
                attestation_share) 
        {
            var k := (attestation_share.data, attestation_share.aggregation_bits);
            var process := f_add_new_attestation_share(
                        process,
                        attestation_share
                    );
                        
            if process.construct_signed_attestation_signature(process.rcvd_attestation_shares[attestation_share.data.slot][k]).isPresent()
            {
                var aggregated_attestation := 
                        Attestation(
                            aggregation_bits := attestation_share.aggregation_bits,
                            data := attestation_share.data,
                            signature := process.construct_signed_attestation_signature(process.rcvd_attestation_shares[attestation_share.data.slot][k]).safe_get()
                        );

                var att_shares := process.rcvd_attestation_shares[attestation_share.data.slot][k];
                assert construct_signed_attestation_signature_assumptions_reverse(
                    process.construct_signed_attestation_signature,
                    process.dv_pubkey,
                    dv.all_nodes                    
                );

                assert process.construct_signed_attestation_signature(att_shares).isPresent();

                assert construct_signed_attestation_signature_assumptions_reverse(
                    process.construct_signed_attestation_signature,
                    process.dv_pubkey,
                    dv.all_nodes
                );

                var data: AttestationData :|
                    construct_signed_attestation_signature_assumptions_reverse_helper(
                        process.construct_signed_attestation_signature,
                        process.dv_pubkey,
                        dv.all_nodes,
                        att_shares,
                        data                
                    );

                var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(data.target.epoch));
                var signing_root := compute_attestation_signing_root(data, fork_version);


                var signers := 
                set signer, att_share | 
                    && att_share in att_shares
                    && signer in dv.all_nodes
                    && verify_bls_signature(signing_root, att_share.signature, signer)
                ::
                    signer;

                assert signers <= dv.all_nodes;

                lemmaThereExistsAnHonestInQuorum(dv.all_nodes, dv.all_nodes - dv.honest_nodes_states.Keys, signers);

                var h_s :| h_s in dv.honest_nodes_states.Keys && h_s in signers;
                var h_s_att :| h_s_att in att_shares && verify_bls_signature(signing_root, h_s_att.signature, h_s);
        
                assert  && h_s in dv.honest_nodes_states.Keys
                        && h_s_att in dv.att_network.allMessagesSent
                        && h_s_att.data == data
                        && verify_bls_signature(signing_root, h_s_att.signature, h_s);

                assert  && h_s in dv.honest_nodes_states.Keys
                        && h_s_att in dv.att_network.allMessagesSent
                        && h_s_att.data == data
                        && verify_bls_signature(signing_root, h_s_att.signature, h_s);

                assert inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(
                                dv,
                                h_s,
                                h_s_att,
                                aggregated_attestation
                            );

                assert f_listen_for_attestation_shares(process, attestation_share).outputs.attestations_submitted == {aggregated_attestation};

                assert forall a | a in f_listen_for_attestation_shares(process, attestation_share).outputs.attestations_submitted ::
                            exists hn', att_share: AttestationShare :: inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(dv, hn', att_share, a);
            }
        }   
    }    

    lemma lem_inv_rcvd_attestation_shares_is_in_all_messages_sent_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,
        s': DVCState,
        dv: DVState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires s' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(dv, process)
    requires attestation_share in dv.att_network.allMessagesSent
    ensures inv_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(dv, s') 
    { }    

    lemma lem_inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_ex_helper(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(s)
    requires s'.all_attestations_created == s.all_attestations_created
    ensures inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');
    {
        forall a |
            && a in s'.all_attestations_created
            && is_valid_attestation(a, s'.dv_pubkey)
        ensures exists hn', att_share: AttestationShare :: inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s', hn', att_share, a);
        {
            var hn', att_share: AttestationShare :|
                inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s, hn', att_share, a);
            
            assert inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s', hn', att_share, a);
            assert exists hn', att_share: AttestationShare :: inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s', hn', att_share, a);
        }
    }    

    // // 1m 10s
    // TODO: simplify this lemma
    lemma lem_inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(s)
    requires construct_signed_attestation_signature_assumptions_helper(
        s.construct_signed_attestation_signature,
        s.dv_pubkey,
        s.all_nodes
    )
    requires inv_only_dv_construct_signed_attestation_signature(s)  
    requires invNetwork(s)
    requires inv_quorum_constraints(s)
    requires inv_rcvd_attestation_shares_is_in_all_messages_sent(s)    
    ensures inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(s')
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        lem_inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_ex_helper(s, event, s');
                        assert inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');  

                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_f_att_consensus_decided_unchanged_dvc_vars(s.honest_nodes_states[node], id, decided_attestation_data, s'.honest_nodes_states[node]);
                        lem_inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_ex_helper(s, event, s');
                        assert inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');            

                    case ReceivedAttestationShare(attestation_share) => 
                        assert multiset(addReceipientToMessages<AttestationShare>({attestation_share}, node)) <= s.att_network.messagesInTransit;

                        assert MessaageWithRecipient(message := attestation_share, receipient := node) in s.att_network.messagesInTransit;      

                        var stateAndOutput := f_listen_for_attestation_shares(s_node, attestation_share);  

                        
                        assert attestation_share in s.att_network.allMessagesSent;
                        assert s'.all_attestations_created == s.all_attestations_created + stateAndOutput.outputs.attestations_submitted;

                        lem_inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_ex_f_listen_for_attestation_shares(
                            s_node,
                            attestation_share,
                            s'_node,
                            s
                        );

                        forall a | 
                                    && a in s'.all_attestations_created
                                    && is_valid_attestation(a, s'.dv_pubkey)
                        ensures exists hn', att_share: AttestationShare :: inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s', hn', att_share, a);            
                        {
                            if a in s.all_attestations_created
                            {
                                var hn', att_share: AttestationShare :| inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s, hn', att_share, a);
                                assert inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s', hn', att_share, a);
                            }
                            else 
                            {
                                assert a in stateAndOutput.outputs.attestations_submitted;
                                var hn', att_share: AttestationShare :| inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s, hn', att_share, a);
                                assert inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s', hn', att_share, a);
                            }                                   
                        }                                

                        assert inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');         

                    case ImportedNewBlock(block) => 
                        var s_node := f_add_block_to_bn(s_node, nodeEvent.block);
                        lem_f_listen_for_new_imported_blocksd_unchanged_dvc_vars(s_node, block, s'_node);
                        assert s'.all_attestations_created == s.all_attestations_created;
                        lem_inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_ex_helper(s, event, s');
                        assert inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');     

                    case ResendAttestationShares => 
                        assert s'.all_attestations_created == s.all_attestations_created;
                        lem_inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_ex_helper(s, event, s');
                        assert inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');

                    case NoEvent => 
                        assert s'.all_attestations_created == s.all_attestations_created;
                        lem_inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_ex_helper(s, event, s');
                        assert inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');
                }

            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                forall a | 
                    && a in s'.all_attestations_created
                    && is_valid_attestation(a, s'.dv_pubkey)
                ensures exists hn', att_share: AttestationShare :: inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s', hn', att_share, a);      
                {
                    if a in s.all_attestations_created
                    {
                        var hn', att_share: AttestationShare :| inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s, hn', att_share, a);
                        assert inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s', hn', att_share, a);                        
                    }
                    else 
                    {
                        var attestation_shares :| 
                            && attestation_shares <= s'.att_network.allMessagesSent
                            // && var sig_shares := set x | x in attestation_shares :: x.signature;
                            && var constructed_sig := s.construct_signed_attestation_signature(attestation_shares);
                            && constructed_sig.isPresent()
                            && constructed_sig.safe_get() == a.signature
                            ;      

                        var constructed_sig := s.construct_signed_attestation_signature(attestation_shares);         

                        var data: AttestationData :|
                            construct_signed_attestation_signature_assumptions_reverse_helper(
                                s.construct_signed_attestation_signature,
                                s.dv_pubkey,
                                s.all_nodes,
                                attestation_shares,
                                data                
                            );   

                        var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(data.target.epoch));
                        var signing_root := compute_attestation_signing_root(data, fork_version);
    

                        var signers := 
                        set signer, att_share | 
                            && att_share in attestation_shares
                            && signer in s.all_nodes
                            && verify_bls_signature(signing_root, att_share.signature, signer)
                        ::
                            signer;            

                        assert signers <= s.all_nodes;

                        lemmaThereExistsAnHonestInQuorum(s.all_nodes, s.all_nodes - s.honest_nodes_states.Keys, signers);  

                        var h_s :| h_s in s.honest_nodes_states.Keys && h_s in signers;
                        var h_s_att :| h_s_att in attestation_shares && verify_bls_signature(signing_root, h_s_att.signature, h_s);     

                        assert 
                        && h_s in s.honest_nodes_states.Keys
                        && h_s_att in s.att_network.allMessagesSent
                        && h_s_att.data == data
                        && verify_bls_signature(signing_root, h_s_att.signature, h_s);

                        assert 
                        && h_s in s.honest_nodes_states.Keys
                        && h_s_att in s.att_network.allMessagesSent
                        && h_s_att.data == data
                        && verify_bls_signature(signing_root, h_s_att.signature, h_s);    

                        compute_signing_root_properties<AttestationData>();
                        lem_verify_bls_signature();

                        var a_fork_version := bn_get_fork_version(compute_start_slot_at_epoch(a.data.target.epoch));
                        var a_attestation_signing_root := compute_attestation_signing_root(a.data, a_fork_version);       

                        assert verify_bls_signature(signing_root, a.signature, s'.dv_pubkey);

                        assert verify_bls_signature(a_attestation_signing_root, a.signature, s'.dv_pubkey);             

                        // assert 

                        assert inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(
                            s,
                            h_s,
                            h_s_att,
                            a
                        );      

                        assert inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(
                            s',
                            h_s,
                            h_s_att,
                            a
                        );                                                                                                                                                 
                    }
                }
                assert inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');
        }
    }        

    lemma lem_inv_rcvd_attestation_shares_is_in_all_messages_sent(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires invNetwork(s)
    requires inv_rcvd_attestation_shares_is_in_all_messages_sent(s)
    ensures inv_rcvd_attestation_shares_is_in_all_messages_sent(s')
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        lem_f_serve_attestation_duty_constants(s_node, attestation_duty, s'_node);

                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_f_att_consensus_decided_unchanged_dvc_vars(s_node, id, decided_attestation_data, s'_node);

                    case ReceivedAttestationShare(attestation_share) => 
                        assert multiset(addReceipientToMessages<AttestationShare>({attestation_share}, node)) <= s.att_network.messagesInTransit;
                        assert MessaageWithRecipient(message := attestation_share, receipient := node) in s.att_network.messagesInTransit;        
                        assert attestation_share in s.att_network.allMessagesSent;                    
                        lem_inv_rcvd_attestation_shares_is_in_all_messages_sent_f_listen_for_attestation_shares(
                            s_node,
                            attestation_share,
                            s'_node,
                            s
                        );

                    case ImportedNewBlock(block) => 
                        var s_node := f_add_block_to_bn(s_node, nodeEvent.block);
                        lem_f_listen_for_new_imported_blocksd_unchanged_dvc_vars(s_node, block, s'_node);
                        assert inv_rcvd_attestation_shares_is_in_all_messages_sent(s');      

                    case ResendAttestationShares => 
                        assert inv_rcvd_attestation_shares_is_in_all_messages_sent(s');                    
                    case NoEvent => 

                }

            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>

        }
    }     

    lemma lem_getMessagesFromEmptySetOfMessagesWithRecipient_is_empty_set<M>(mswr: set<MessaageWithRecipient<M>>)
    requires mswr == {}
    ensures getMessagesFromMessagesWithRecipient(mswr) == {}
    {
    }

    // TODO
    lemma lem_inv_data_of_att_share_is_decided_value_helper(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_data_of_att_share_is_decided_value(s)
    requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    requires inv_quorum_constraints(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires |s.all_nodes| > 0
    requires s'.att_network.allMessagesSent == 
                    s.att_network.allMessagesSent + getMessagesFromMessagesWithRecipient({});
    ensures  inv_data_of_att_share_is_decided_value(s');
    {
        forall cid | cid in s.consensus_on_attestation_data.Keys 
        ensures && var s_consensus := s.consensus_on_attestation_data[cid];
                && var s'_consensus := s'.consensus_on_attestation_data[cid];
                && s_consensus.decided_value.isPresent() ==> 
                        ( && s'_consensus.decided_value.isPresent()
                          && s_consensus.decided_value.safe_get() == s'_consensus.decided_value.safe_get()
                        )
            ;
        {
            var s_consensus := s.consensus_on_attestation_data[cid];
            var s'_consensus := s'.consensus_on_attestation_data[cid];

            assert isConditionForSafetyTrue(s_consensus);
            assert s_consensus.decided_value.isPresent() ==> 
                && s'_consensus.decided_value.isPresent()
                && s_consensus.decided_value.safe_get() == s'_consensus.decided_value.safe_get()
            ;
        }

        assert forall cid | cid in s.consensus_on_attestation_data.Keys :: 
                    && var s_consensus := s.consensus_on_attestation_data[cid];
                    && var s'_consensus := s'.consensus_on_attestation_data[cid];
                    && s_consensus.decided_value.isPresent() ==> 
                            ( && s'_consensus.decided_value.isPresent()
                            && s_consensus.decided_value.safe_get() == s'_consensus.decided_value.safe_get()
                            )
        ;

        var emptySet: set<MessaageWithRecipient<AttestationShare>> := {};
        calc {
            s'.att_network.allMessagesSent;
            == 
            s.att_network.allMessagesSent + getMessagesFromMessagesWithRecipient(emptySet);
            ==
            {lem_getMessagesFromEmptySetOfMessagesWithRecipient_is_empty_set(emptySet);}
            s.att_network.allMessagesSent;
        }

        assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent;        

        forall hn, att_share |
                && hn in s'.honest_nodes_states.Keys 
                && att_share in s'.att_network.allMessagesSent
                && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));                
                && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
                && verify_bls_signature(attestation_signing_root, att_share.signature, hn)
        ensures inv_data_of_att_share_is_decided_value_body(s', att_share);
        {
            assert att_share in s.att_network.allMessagesSent;
            assert inv_data_of_att_share_is_decided_value_body(s, att_share);
            assert inv_data_of_att_share_is_decided_value_body(s', att_share);
        }

        assert inv_data_of_att_share_is_decided_value(s');   
    }     

    lemma lem_consensus_next_under_safety<D(!new, 0)>(
        s: ConsensusInstance,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,        
        s': ConsensusInstance,
        output: Optional<OutCommand>
    )
    requires ConsensusSpec.Next(s, honest_nodes_validity_predicates, s', output)
    requires isConditionForSafetyTrue(s)
    requires s.decided_value.isPresent()
    ensures s'.decided_value.isPresent()
    ensures s.decided_value.safe_get() == s'.decided_value.safe_get()
    { }

    

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_get_s_w_honest_node_states_updated(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Types.Event
    ) returns (s_w_honest_node_states_updated: DVState)
    requires node in s.honest_nodes_states
    ensures s_w_honest_node_states_updated == add_block_to_bn_with_event(s, node, nodeEvent)
    ensures s_w_honest_node_states_updated == s.(honest_nodes_states := s_w_honest_node_states_updated.honest_nodes_states)
    ensures s_w_honest_node_states_updated.honest_nodes_states == s.honest_nodes_states[node := s_w_honest_node_states_updated.honest_nodes_states[node]]
    ensures s_w_honest_node_states_updated.honest_nodes_states[node] == s.honest_nodes_states[node].(bn := s_w_honest_node_states_updated.honest_nodes_states[node].bn)
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

    lemma  lemmaNextConsensus<D(!new, 0)>(
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

    lemma  lemmaNextConsensus2<D(!new, 0)>(
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

    lemma lem_inv_data_of_att_share_is_decided_value_att_consensus_decided_helper_2(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event.event.AttConsensusDecided?
    requires inv_quorum_constraints(s)
    requires inv_unchanged_paras_of_consensus_instances(s)        
    requires |s.all_nodes| > 0    
    ensures s'.consensus_on_attestation_data[event.event.id].decided_value.safe_get() == event.event.decided_attestation_data; 
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case AttConsensusDecided(id: Slot, decided_attestation_data) => 
                        var s_w_honest_node_states_updated := lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_get_s_w_honest_node_states_updated(s, node, nodeEvent);           
                        var cid := id;

                        assert s_w_honest_node_states_updated.consensus_on_attestation_data == s.consensus_on_attestation_data;

                        var output := Some(Decided(node, nodeEvent.decided_attestation_data)); 

                        var validityPredicates := 
                                map n |
                                        && n in s_w_honest_node_states_updated.honest_nodes_states.Keys 
                                        && cid in s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
                                    ::
                                        s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances[cid].validityPredicate
                                ;

                        var s_consensus := s_w_honest_node_states_updated.consensus_on_attestation_data[cid];
                        var s'_consensus := s'.consensus_on_attestation_data[cid];                

                        assert ConsensusSpec.Next(
                                    s_consensus,
                                    validityPredicates,
                                    s'_consensus,
                                    output
                                );                               

                        assert s'.consensus_on_attestation_data[id].decided_value.isPresent();
                        assert isConditionForSafetyTrue(s'_consensus);
                        assert s'_consensus.decided_value.safe_get() == decided_attestation_data; 
                        assert s'.consensus_on_attestation_data[id].decided_value.safe_get() == decided_attestation_data; 
                }
        }            
    }

    // // 1m 15s
    lemma lem_inv_decided_value_of_consensus_instance_is_decided_by_quorum_helper(
        s: DVState,
        event: DV.Event,
        cid: Slot,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires cid in s'.consensus_on_attestation_data.Keys
    requires inv_quorum_constraints(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)    
    requires s.consensus_on_attestation_data[cid].decided_value.isPresent()
    ensures is_a_valid_decided_value(s'.consensus_on_attestation_data[cid]); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
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

                
                assert isConditionForSafetyTrue(s_consensus);
                assert && s'_consensus.decided_value.isPresent()
                       && s_consensus.decided_value.safe_get() == s'_consensus.decided_value.safe_get()
                       ;

                var h_nodes :| is_a_valid_decided_value_according_to_set_of_nodes(s_consensus, h_nodes); 

                assert s_consensus.honest_nodes_validity_functions.Keys <= s'_consensus.honest_nodes_validity_functions.Keys;
                assert         
                    && var byz := s'.all_nodes - s'_consensus.honest_nodes_status.Keys;
                    |h_nodes| >= quorum(|s.all_nodes|) - |byz|;

                lemmaNextConsensus(
                    s_consensus,
                    validityPredicates,
                    s'_consensus,
                    output                        
                );


                forall n | n in h_nodes 
                ensures exists vp: AttestationData -> bool :: vp in s'_consensus.honest_nodes_validity_functions[n] && vp(s'_consensus.decided_value.safe_get());
                {
                    assert is_a_valid_decided_value(s_consensus); 
                    var vp: AttestationData -> bool :| vp in s_consensus.honest_nodes_validity_functions[n] && vp(s_consensus.decided_value.safe_get()); 
                    lemmaNextConsensus2(
                        s_consensus,
                        validityPredicates,
                        s'_consensus,
                        output,
                        n                       
                    );                        
                    assert vp in  s'_consensus.honest_nodes_validity_functions[n]; 
                    assert vp(s'_consensus.decided_value.safe_get());
                    assert exists vp: AttestationData -> bool :: vp in s'_consensus.honest_nodes_validity_functions[n] && vp(s'_consensus.decided_value.safe_get());
                }

                assert is_a_valid_decided_value_according_to_set_of_nodes(s'_consensus, h_nodes); 
                assert is_a_valid_decided_value(s'_consensus); 
        }
    }   

    lemma lem_inv_decided_value_of_consensus_instance_is_decided_by_quorum(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_quorum_constraints(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)    
    ensures inv_decided_value_of_consensus_instance_is_decided_by_quorum(s')   
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
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
                        && cid in s'.consensus_on_attestation_data.Keys
                        && s'.consensus_on_attestation_data[cid].decided_value.isPresent()
                ensures is_a_valid_decided_value(s'.consensus_on_attestation_data[cid]);
                {
                    if s.consensus_on_attestation_data[cid].decided_value.isPresent()
                    {
                        lem_inv_decided_value_of_consensus_instance_is_decided_by_quorum_helper(s, event, cid, s');
                    }
                    else
                    {
                        assert is_a_valid_decided_value(s'.consensus_on_attestation_data[cid]);
                    }
                }
                assert inv_decided_value_of_consensus_instance_is_decided_by_quorum(s');
               

            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                assert inv_decided_value_of_consensus_instance_is_decided_by_quorum(s');
        }        
    } 

    lemma lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k_helper(
        s: DVState,
        cid: Slot
    )
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(s)
    requires inv_quorum_constraints(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires cid in s.consensus_on_attestation_data.Keys
    requires s.consensus_on_attestation_data[cid].decided_value.isPresent()
    ensures s.consensus_on_attestation_data[cid].decided_value.safe_get().slot == cid
    {
        var s_consensus := s.consensus_on_attestation_data[cid];
        assert is_a_valid_decided_value(s_consensus);  

        var h_nodes_a :| is_a_valid_decided_value_according_to_set_of_nodes(s_consensus, h_nodes_a);

        var byz := s.all_nodes - s.honest_nodes_states.Keys;

        assert byz * h_nodes_a == {} by 
        {
            assert s.honest_nodes_states.Keys * byz == {};
        }

        lemmaThereExistsAnHonestInQuorum2(s.all_nodes, byz, h_nodes_a);  

        var h_n :| h_n in h_nodes_a;  

        var vp: AttestationData -> bool :| vp in s_consensus.honest_nodes_validity_functions[h_n] && vp(s_consensus.decided_value.safe_get());  

        var attestation_duty, attestation_slashing_db :|
                inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_body(cid, attestation_duty, attestation_slashing_db, vp);

        assert s_consensus.decided_value.safe_get().slot == cid;
    }

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_get_s_w_honest_node_states_updated_2(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Types.Event,
        node': BLSPubkey,
        s_w_honest_node_states_updated: DVState
    ) 
    requires node in s.honest_nodes_states
    requires node' in s.honest_nodes_states
    requires s_w_honest_node_states_updated == add_block_to_bn_with_event(s, node, nodeEvent)
    ensures s_w_honest_node_states_updated.honest_nodes_states[node'].attestation_consensus_engine_state == s.honest_nodes_states[node'].attestation_consensus_engine_state
    {      
    }  

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_helper(
        s: DVState,
        event: DV.Event,
        s': DVState,
        cid: Slot,
        hn: BLSPubkey,
        vp: AttestationData -> bool
    )   returns (attestation_duty: AttestationDuty, attestation_slashing_db: set<SlashingDBAttestation>)
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')    
    requires inv_quorum_constraints(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)      
    requires
            && hn in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions.Keys
            && vp in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions[hn]
    requires event.HonestNodeTakingStep?
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(s)
    ensures inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_body(cid, attestation_duty, attestation_slashing_db, vp); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];

                var s_w_honest_node_states_updated :=
                    lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_get_s_w_honest_node_states_updated(s, node, nodeEvent);         

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

            if hn in s_consensus.honest_nodes_validity_functions.Keys  && vp in s_consensus.honest_nodes_validity_functions[hn]
            {
                assert vp in s'_consensus.honest_nodes_validity_functions[hn];

                attestation_duty, attestation_slashing_db :| inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_body(cid, attestation_duty, attestation_slashing_db, vp);

            }
            else 
            {
                assert vp in validityPredicates.Values;
                var vpn :| vpn in validityPredicates.Keys && validityPredicates[vpn] == vp;
                assert validityPredicates[vpn] == s_w_honest_node_states_updated.honest_nodes_states[vpn].attestation_consensus_engine_state.active_attestation_consensus_instances[cid].validityPredicate;

                assert vpn in s.honest_nodes_states.Keys;
                assert cid in s_w_honest_node_states_updated.honest_nodes_states[vpn].attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

                lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_get_s_w_honest_node_states_updated_2(s, node, nodeEvent, vpn, s_w_honest_node_states_updated);

                assert s_w_honest_node_states_updated.honest_nodes_states[vpn].attestation_consensus_engine_state == s.honest_nodes_states[vpn].attestation_consensus_engine_state;
                assert inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc(s, vpn, cid);

                attestation_duty, attestation_slashing_db :| inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_body(cid, attestation_duty, attestation_slashing_db, vp);
            }

            assert inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_body(cid, attestation_duty, attestation_slashing_db, vp);


        }

    }  

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(
        s: DVState,
        event: DV.Event,
        s': DVState
    )   
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')    
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(s)
    requires inv_quorum_constraints(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)      
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(s)  
    ensures inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(s')   
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                forall hn, cid: Slot, vp |
                    && hn in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions.Keys
                    && vp in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions[hn]
                ensures exists attestation_duty, attestation_slashing_db :: inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_body(cid, attestation_duty, attestation_slashing_db, vp)
                {
                    var attestation_duty: AttestationDuty, attestation_slashing_db := lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_helper(s, event, s', cid, hn, vp);
                }
                assert inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(s');

            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                assert inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(s');
        }
    }   

    lemma lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(s)  
    requires inv_quorum_constraints(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)  
    ensures inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s') 
    {
        lem_inv_quorum_constraints_dv_next(s, event, s');
        lem_inv_unchanged_paras_of_consensus_instances_dv_next(s, event, s');
        lem_inv_only_dv_construct_signed_attestation_signature_dv_next(s, event, s');
        lem_inv_decided_value_of_consensus_instance_is_decided_by_quorum(s, event, s');
        lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(s, event, s');
        lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k2(s');   
    }     

    lemma lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k2(
        s: DVState
    )
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(s)
    requires inv_quorum_constraints(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    ensures inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s) 
    {
        forall cid |
            && cid in s.consensus_on_attestation_data.Keys
            && s.consensus_on_attestation_data[cid].decided_value.isPresent()
        {
           lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k_helper(s, cid);
        }        
    }       

    // 2 min    
    // TODO: Simplify
    lemma lem_inv_data_of_att_share_is_decided_value_att_consensus_decided(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event.event.AttConsensusDecided?
    requires inv_data_of_att_share_is_decided_value(s)
    requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)  
    requires inv_quorum_constraints(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(s)          
    requires |s.all_nodes| > 0
    ensures inv_data_of_att_share_is_decided_value(s')   
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var process := s.honest_nodes_states[node];
                var process' := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case AttConsensusDecided(id: Slot, decided_attestation_data) => 
                        if  && process.current_attestation_duty.isPresent()
                            && id == process.current_attestation_duty.safe_get().slot
                            && id == decided_attestation_data.slot
                        {
                            var attestation_with_signature_share := f_calc_att_with_sign_share_from_decided_att_data(
                                                                        process,
                                                                        id,
                                                                        decided_attestation_data
                                                                    );       
                            var messagesToBeSent := f_att_consensus_decided(process, id, decided_attestation_data).outputs.att_shares_sent;

                            assert messagesToBeSent ==  multicast(attestation_with_signature_share, process.peers);  
                            assert s'.att_network.allMessagesSent == 
                                        s.att_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent); 
                            assert forall m | m in messagesToBeSent :: m.message == attestation_with_signature_share; 

                            lemmaOnGetMessagesFromMessagesWithRecipientWhenAllMessagesAreTheSame(messagesToBeSent, attestation_with_signature_share);    
                            assert getMessagesFromMessagesWithRecipient(messagesToBeSent) ==  {attestation_with_signature_share};
                            assert s'.att_network.allMessagesSent == 
                                        s.att_network.allMessagesSent + { attestation_with_signature_share }; 

                            forall hn, att_share |
                                    && hn in s'.honest_nodes_states.Keys 
                                    && att_share in s'.att_network.allMessagesSent
                                    && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));
                                    && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
                                    && verify_bls_signature(attestation_signing_root, att_share.signature, hn)
                            ensures s'.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent();
                            ensures s'.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;     
                            {
                                // lem_inv_data_of_att_share_is_decided_value_att_consensus_decided_helper(s, event, s', hn, att_share);
                                if att_share in s.att_network.allMessagesSent
                                {
                                    lem_inv_data_of_att_share_is_decided_value_att_consensus_decided_helper_1(s, event, s', hn, att_share);    
                                }
                                else
                                {
                                    assert att_share == attestation_with_signature_share;
                                    lemmaImaptotalElementInDomainIsInKeys(s.consensus_on_attestation_data, id);
                                    assert id in s.consensus_on_attestation_data.Keys ;
                                    lem_inv_data_of_att_share_is_decided_value_att_consensus_decided_helper_2(s, event, s');

                                    assert s'.consensus_on_attestation_data[id].decided_value.safe_get() == decided_attestation_data; 
                                    assert s'.consensus_on_attestation_data[id].decided_value.safe_get() == att_share.data; 
                                    lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s, event, s');   
                                    
                                    assert att_share.data.slot == id;
                                    assert s'.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent();                             
                                    assert s'.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data; 
                                } 
                            }           

                            assert inv_data_of_att_share_is_decided_value(s');
                        }
                        else 
                        {
                            forall hn, att_share |
                                    && hn in s'.honest_nodes_states.Keys 
                                    && att_share in s'.att_network.allMessagesSent
                                    && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));
                                    && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
                                    && verify_bls_signature(attestation_signing_root, att_share.signature, hn)
                            ensures s'.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent();
                            ensures s'.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;     
                            {
                                assert att_share in s.att_network.allMessagesSent;
                                lem_inv_data_of_att_share_is_decided_value_att_consensus_decided_helper_1(s, event, s', hn, att_share);
                            } 

                            assert inv_data_of_att_share_is_decided_value(s');
                        }
                }
        }
    }

    lemma lem_inv_data_of_att_share_is_decided_value_att_adversary(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.AdeversaryTakingStep?
    requires inv_data_of_att_share_is_decided_value(s)
    requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)  
    requires inv_quorum_constraints(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires |s.all_nodes| > 0
    ensures inv_data_of_att_share_is_decided_value(s') 
    {
        var new_attestation_shares_sent := s'.att_network.allMessagesSent - s.att_network.allMessagesSent;

        forall hn, att_share |
                && hn in s'.honest_nodes_states.Keys 
                && att_share in s'.att_network.allMessagesSent
                && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));
                && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
                && verify_bls_signature(attestation_signing_root, att_share.signature, hn)
        ensures s'.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent();
        ensures s'.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;                          
        {
            var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));
            var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);        

            if att_share in s.att_network.allMessagesSent
            {
                assert s.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent();
                assert s.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;   
            }
            else
            {
                forall signer | verify_bls_signature(attestation_signing_root, att_share.signature, signer)
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
    
        assert inv_data_of_att_share_is_decided_value(s');
    }      

    lemma lem_inv_data_of_att_share_is_decided_value_helper2<M>(
        allMessagesSent': set<M>,
        allMessagesSent: set<M>,
        messagesToBeSent: set<MessaageWithRecipient<M>>
    )
    requires allMessagesSent' == allMessagesSent + 
                                getMessagesFromMessagesWithRecipient(messagesToBeSent);
    requires messagesToBeSent == {}
    ensures allMessagesSent' == allMessagesSent
    { }

       

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_updateConsensusInstanceValidityCheckHelper(
        m: map<Slot, AttestationConsensusValidityCheckState>,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        m': map<Slot, AttestationConsensusValidityCheckState>
    )    
    requires m' == updateConsensusInstanceValidityCheckHelper(m, new_attestation_slashing_db)
    requires forall k | k in m :: inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_body_body(k, m[k].attestation_duty, m[k].validityPredicate)
    ensures forall k | k in m' :: inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_body_body(k, m'[k].attestation_duty, m'[k].validityPredicate)    
    {
        forall k | k in  m 
        ensures k in m'
        {
            lemmaMapKeysHasOneEntryInItems(m, k);
            assert k in m';
        }

        assert m.Keys == m'.Keys;

        forall k | k in m' 
        ensures inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_body(k, m'[k].attestation_duty, new_attestation_slashing_db, m'[k].validityPredicate); 
        {
            assert m'[k] == m[k].(
                    validityPredicate := (ad: AttestationData) => consensus_is_valid_attestation_data(new_attestation_slashing_db, ad, m[k].attestation_duty)
            );
            assert  inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_body(k, m'[k].attestation_duty, new_attestation_slashing_db, m'[k].validityPredicate);        
        }
    }

    
    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_duty_updateConsensusInstanceValidityCheck(
        s: ConsensusEngineState,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState
    )    
    requires s' == updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db)
    ensures s'.active_attestation_consensus_instances.Keys == s.active_attestation_consensus_instances.Keys
    ensures s'.att_slashing_db_hist.Keys == s.att_slashing_db_hist.Keys + s'.active_attestation_consensus_instances.Keys;
    {
        lem_updateConsensusInstanceValidityCheckHelper(s.active_attestation_consensus_instances, new_attestation_slashing_db, s'.active_attestation_consensus_instances);

        assert s'.att_slashing_db_hist.Keys == s.att_slashing_db_hist.Keys + s'.active_attestation_consensus_instances.Keys;

        assert forall slot, vp: AttestationData -> bool |
                    && slot in s.att_slashing_db_hist.Keys 
                    && vp in s.att_slashing_db_hist[slot].Keys
                    ::
                    && s.att_slashing_db_hist.Keys <= s'.att_slashing_db_hist.Keys
                    && s.att_slashing_db_hist[slot].Keys <= s'.att_slashing_db_hist[slot].Keys
                    && s.att_slashing_db_hist[slot][vp] <= s'.att_slashing_db_hist[slot][vp]
        ;

        assert forall slot |
                    && slot in s'.active_attestation_consensus_instances.Keys 
                    && slot in s.att_slashing_db_hist.Keys
                    && var vp := s'.active_attestation_consensus_instances[slot].validityPredicate;
                    && vp in s.att_slashing_db_hist[slot].Keys
                    ::
                    var vp := s'.active_attestation_consensus_instances[slot].validityPredicate;
                    s.att_slashing_db_hist[slot][vp] + {new_attestation_slashing_db} == s'.att_slashing_db_hist[slot][vp];      

        assert forall slot, vp: AttestationData -> bool |
                    && slot in s'.att_slashing_db_hist.Keys 
                    && slot !in s.att_slashing_db_hist.Keys 
                    && vp in s'.att_slashing_db_hist[slot].Keys
                    ::
                    && vp == s'.active_attestation_consensus_instances[slot].validityPredicate
        ;      

        assert forall slot, vp: AttestationData -> bool |
                    && slot in s.att_slashing_db_hist.Keys 
                    && vp in s'.att_slashing_db_hist[slot].Keys
                    && vp !in s.att_slashing_db_hist[slot].Keys
                    ::
                    && s'.att_slashing_db_hist[slot][vp] == {new_attestation_slashing_db}
        ;     
                   
    }   

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_duty_updateConsensusInstanceValidityCheck2(
        s: ConsensusEngineState,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState,
        slot: Slot,
        vp: AttestationData -> bool 
    )    
    requires s' == updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db)
    requires 
                    && slot in s'.active_attestation_consensus_instances.Keys 
                    && slot in s.att_slashing_db_hist.Keys
                    && vp == s'.active_attestation_consensus_instances[slot].validityPredicate
                    && vp in s.att_slashing_db_hist[slot].Keys  
    ensures s.att_slashing_db_hist[slot][vp] + {new_attestation_slashing_db} == s'.att_slashing_db_hist[slot][vp];      
    {
        lem_updateConsensusInstanceValidityCheckHelper(s.active_attestation_consensus_instances, new_attestation_slashing_db, s'.active_attestation_consensus_instances);

        assert s'.att_slashing_db_hist.Keys == s.att_slashing_db_hist.Keys + s'.active_attestation_consensus_instances.Keys;                   
    }   

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_duty_updateConsensusInstanceValidityCheck3(
        s: ConsensusEngineState,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState,
        slot: Slot,
        vp: AttestationData -> bool 
    )    
    requires s' == updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db)
    requires 
                    && slot in s'.active_attestation_consensus_instances.Keys 
                    && slot in s.att_slashing_db_hist.Keys
                    && vp != s'.active_attestation_consensus_instances[slot].validityPredicate
                    && vp in s.att_slashing_db_hist[slot].Keys  
    ensures s.att_slashing_db_hist[slot][vp] == s'.att_slashing_db_hist[slot][vp];      
    {
        lem_updateConsensusInstanceValidityCheckHelper(s.active_attestation_consensus_instances, new_attestation_slashing_db, s'.active_attestation_consensus_instances);

        assert s'.att_slashing_db_hist.Keys == s.att_slashing_db_hist.Keys + s'.active_attestation_consensus_instances.Keys;                   
    }      

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_duty_updateConsensusInstanceValidityCheck4(
        s: ConsensusEngineState,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState,
        slot: Slot,
        vp: AttestationData -> bool 
    )    
    requires s' == updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db)
    requires 
                    && slot !in s'.active_attestation_consensus_instances.Keys 
                    && slot in s.att_slashing_db_hist.Keys
                    && vp in s.att_slashing_db_hist[slot].Keys  
    ensures s.att_slashing_db_hist[slot][vp] == s'.att_slashing_db_hist[slot][vp];      
    {
        lem_updateConsensusInstanceValidityCheckHelper(s.active_attestation_consensus_instances, new_attestation_slashing_db, s'.active_attestation_consensus_instances);

        assert s'.att_slashing_db_hist.Keys == s.att_slashing_db_hist.Keys + s'.active_attestation_consensus_instances.Keys;                   
    }   

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_duty_updateConsensusInstanceValidityCheck5(
        s: ConsensusEngineState,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState,
        slot: Slot    
    )    
    requires s' == updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db)
    requires slot in s.att_slashing_db_hist.Keys
    ensures slot in s'.att_slashing_db_hist.Keys
    ensures s.att_slashing_db_hist[slot].Keys <= s'.att_slashing_db_hist[slot].Keys;      
    {
        lem_updateConsensusInstanceValidityCheckHelper(s.active_attestation_consensus_instances, new_attestation_slashing_db, s'.active_attestation_consensus_instances);

        assert s'.att_slashing_db_hist.Keys == s.att_slashing_db_hist.Keys + s'.active_attestation_consensus_instances.Keys;                   
    }    

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_f_terminate_current_attestation_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2(process)
    ensures inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2(process')
    { }       

    // TODO: new proof
    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_f_check_for_next_duty_helper(
        process: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires s' == f_check_for_next_duty(process, attestation_duty).state   
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2(process) 
    // ensures  inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2(s')
    {
        var attestation_slashing_db := process.attestation_slashing_db;

        var acvc := AttestationConsensusValidityCheckState(
            attestation_duty := attestation_duty,
            validityPredicate := (ad: AttestationData) => consensus_is_valid_attestation_data(attestation_slashing_db, ad, attestation_duty)
        );     

        // assert s'.attestation_consensus_engine_state.active_attestation_consensus_instances == process.attestation_consensus_engine_state.active_attestation_consensus_instances[attestation_duty.slot := acvc];


        forall cid | cid in s'.attestation_consensus_engine_state.active_attestation_consensus_instances  
            // ensures inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_body(s', cid); 
        {
            if cid != attestation_duty.slot 
            {
                assert cid in process.attestation_consensus_engine_state.active_attestation_consensus_instances;
                // assert inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_body(s', cid); 
            }
            else 
            {
                assert inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_body(
                    cid,
                    attestation_duty,
                    attestation_slashing_db,
                    acvc.validityPredicate
                );
                assert inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_body(s', cid); 
            }
        }   
    }

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_f_start_next_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2(process) 
    ensures inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2(process')
    {
        var new_process := f_new_process_after_starting_new_att_duty(process, attestation_duty);

        assert { attestation_duty.slot } ==
                     new_process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys - 
                            process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

        forall cid | cid in new_process.attestation_consensus_engine_state.active_attestation_consensus_instances
        ensures inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_body(new_process, cid) 
        { 
            if cid in process.attestation_consensus_engine_state.active_attestation_consensus_instances
            {
                assert inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_body(new_process, cid);
            }
            else
            {
                assert cid == attestation_duty.slot;
                
                var acvc := AttestationConsensusValidityCheckState(
                    attestation_duty := attestation_duty,
                    validityPredicate := (ad: AttestationData) => consensus_is_valid_attestation_data(process.attestation_slashing_db, ad, attestation_duty)
                );

                assert acvc == process'.attestation_consensus_engine_state.active_attestation_consensus_instances[cid];
                assert inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_body(cid, attestation_duty, process.attestation_slashing_db, acvc.validityPredicate);    
                assert inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_body_body(cid, attestation_duty, acvc.validityPredicate);
                assert inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_body(new_process, cid);
            }
        }
    }
    
    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_f_check_for_next_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state   
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2(process) 
    ensures inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2(process'); 
    {
        if pred_decision_of_att_duty_was_known(process, attestation_duty)
        {                
            var new_process := f_new_process_after_updateConsensusInstanceValidityCheck(process, attestation_duty);

            lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_updateConsensusInstanceValidityCheckHelper(
                    process.attestation_consensus_engine_state.active_attestation_consensus_instances,
                    new_process.attestation_slashing_db,
                    new_process.attestation_consensus_engine_state.active_attestation_consensus_instances
            );
        }
        else 
        {
            lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_f_start_next_duty(
                process,
                attestation_duty,
                process'
            );                
        }    
    }        

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        process': DVCState
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state  
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2(process) 
    ensures inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2(process'); 
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_f_terminate_current_attestation_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );        
    }        

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(process, id, decided_attestation_data).state
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2(process) 
    ensures inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2(s'); 
    {
        if  is_decided_data_for_current_slot(process, decided_attestation_data, id)
        {
            var s_mod := f_update_process_after_att_duty_decided(
                            process,
                            id,
                            decided_attestation_data);

            lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_updateConsensusInstanceValidityCheckHelper(
                    process.attestation_consensus_engine_state.active_attestation_consensus_instances,
                    s_mod.attestation_slashing_db,
                    s_mod.attestation_consensus_engine_state.active_attestation_consensus_instances
            );            
        }            
    }     

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        s': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2(process) 
    ensures inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2(s');     
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var process := f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                process,
                                block
                            );

        if pred_listen_for_new_imported_blocks_checker(process, att_consensus_instances_already_decided)
        {
            var s_mod := f_updateConsensusInstanceValidityCheck_in_listen_for_new_imported_blocks(
                                    process,
                                    att_consensus_instances_already_decided
                                );

            lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_updateConsensusInstanceValidityCheckHelper(
                    process.attestation_consensus_engine_state.active_attestation_consensus_instances,
                    s_mod.attestation_slashing_db,
                    s_mod.attestation_consensus_engine_state.active_attestation_consensus_instances
            );            
        }
    }      

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(
        s: DVState,
        event: DV.Event,
        s': DVState
    )   
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')    
    requires inv_quorum_constraints(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)      
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(s)  
    ensures inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(s')    
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        forall n | n in s'.honest_nodes_states
                        ensures inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2(s'.honest_nodes_states[n]); 
                        {
                            if n == node
                            {
                                lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_f_serve_attestation_duty(s_node, attestation_duty, s'_node);
                                assert inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2(s'_node); 
                            }
                        }
                        assert inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(s');                        
                  
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        forall n | n in s'.honest_nodes_states
                        ensures inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2(s'.honest_nodes_states[n]); 
                        {
                            if n == node
                            {
                                lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2_f_att_consensus_decided(s_node, id, decided_attestation_data, s'_node);
                                assert inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2(s'_node); 
                            }
                        }
                        assert inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(s');                       
              
                    case ReceivedAttestationShare(attestation_share) => 
                        forall n | n in s'.honest_nodes_states
                        ensures s'.honest_nodes_states[n].attestation_consensus_engine_state == s.honest_nodes_states[n].attestation_consensus_engine_state
                        {
                            if n == node
                            {
                                lem_f_listen_for_attestation_shares_unchanged_dvc_vars(s_node, attestation_share, s'_node);
                            }
                        }
                        assert inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(s');     

                    case ImportedNewBlock(block) => 
                        forall n | n in s'.honest_nodes_states
                        ensures inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2(s'.honest_nodes_states[n]); 
                        {
                            if n == node
                            {
                                var s_node := f_add_block_to_bn(s_node, nodeEvent.block);
                                lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_f_listen_for_new_imported_blocks(s_node, block, s'_node);
                                assert inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dvc_single_dvc_2(s'_node); 
                            }
                        }
                        assert inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(s');                        
               
                    case ResendAttestationShares => 
                        assert inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(s');
                   
                    case NoEvent => 
                        assert inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(s');
                }            


            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                assert inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(s');
        }        
    } 

    lemma lem_f_listen_for_new_imported_blocks_helper_1(
        dv: DVState,
        process: DVCState,
        block: BeaconBlock,
        new_consensus_instances_already_decided: map<Slot, AttestationData>
    )
    requires f_listen_for_new_imported_blocks_helper_1.requires(process, block)
    requires new_consensus_instances_already_decided == f_listen_for_new_imported_blocks_helper_1(process, block)
    requires inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv)
    requires inv_data_of_att_share_is_decided_value(dv)
    requires pred_axiom_is_my_attestation_2(dv, process, block)
    ensures forall slot | 
                slot in new_consensus_instances_already_decided
                :: 
                && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                && dv.consensus_on_attestation_data[slot].decided_value.safe_get() == new_consensus_instances_already_decided[slot]
                ;  
    {
        forall slot | slot in new_consensus_instances_already_decided
        ensures 
            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
            && dv.consensus_on_attestation_data[slot].decided_value.safe_get() == new_consensus_instances_already_decided[slot]
            ;         
        {

            var valIndex := bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);


            var a :| 
                && a in block.body.attestations
                && DVC_Spec_NonInstr.isMyAttestation(a, process.bn, block, valIndex)
                && a.data == new_consensus_instances_already_decided[slot]
            ;

            var a' :|
                && a' in dv.all_attestations_created
                && a'.data == a.data 
                && is_valid_attestation(a', dv.dv_pubkey);    

            var hn', att_share: AttestationShare :| inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(dv, hn', att_share, a');

            assert
            && dv.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent()
            && dv.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;

            assert
            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
            && dv.consensus_on_attestation_data[slot].decided_value.safe_get() == new_consensus_instances_already_decided[slot]
            ;              
        }
    }  

    lemma lem_inv_sequence_attestation_duties_to_be_served_orderd_dv_next(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_sequence_attestation_duties_to_be_served_orderd(s)
    ensures inv_sequence_attestation_duties_to_be_served_orderd(s')
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                assert s'.sequence_attestation_duties_to_be_served == s.sequence_attestation_duties_to_be_served;
            
            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                assert s'.sequence_attestation_duties_to_be_served == s.sequence_attestation_duties_to_be_served;
        }
        assert s'.sequence_attestation_duties_to_be_served == s.sequence_attestation_duties_to_be_served;

    }

    // TODO: Simplify
    lemma lem_inv_data_of_att_share_is_decided_value_att_consensus_decided_helper_1(
        s: DVState,
        event: DV.Event,
        s': DVState,
        hn: BLSPubkey,
        att_share: AttestationShare
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event.event.AttConsensusDecided?
    requires inv_data_of_att_share_is_decided_value(s)
    requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)  
    requires inv_quorum_constraints(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(s)          
    requires |s.all_nodes| > 0    
    requires is_correct_att_share(s, hn, att_share)
    requires att_share in s.att_network.allMessagesSent
    ensures && s'.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent()                                     
            && s'.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case AttConsensusDecided(id: Slot, decided_attestation_data) => 
                        assert att_share in s.att_network.allMessagesSent;
                        assert inv_data_of_att_share_is_decided_value(s);
                        assert inv_data_of_att_share_is_decided_value_body(s, att_share);
                        assert s.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent();
                        assert s.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;   

                        var s_w_honest_node_states_updated := lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_get_s_w_honest_node_states_updated(s, node, nodeEvent);           
                        var cid := att_share.data.slot;

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

                        lem_consensus_next_under_safety(
                            s_consensus,
                            validityPredicates,
                            s'_consensus,
                            output                                
                        );                        
                            
                        assert s'.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent();
                        assert s.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == s'.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get();
                            assert s'.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;
                }
        }
    }

    // // Ver time: 1m 35s
    // IMPORTANT: Seem to be an error of Dafny with the second match expression
    // lemma lem_inv_data_of_att_share_is_decided_value(
    //     s: DVState,
    //     event: DV.Event,
    //     s': DVState
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')  
    // requires inv_quorum_constraints(s)
    // requires inv_unchanged_paras_of_consensus_instances(s)
    // requires same_honest_nodes_in_dv_and_ci(s)
    // requires inv_only_dv_construct_signed_attestation_signature(s)
    // requires inv_data_of_att_share_is_decided_value(s)
    // requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    // requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)      
    // requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)    
    // requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(s)    
    // requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(s)          
    // requires |s.all_nodes| > 0
    // // ensures inv_data_of_att_share_is_decided_value(s')   
    // {
    //     match event 
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             var s_node := s.honest_nodes_states[node];
    //             var s'_node := s'.honest_nodes_states[node];
    //             if nodeEvent.AttConsensusDecided? 
    //             {
    //                 // lem_inv_data_of_att_share_is_decided_value_att_consensus_decided(s, event, s');
    //             }
    //             else 
    //             {
    //                 match nodeEvent
    //                 {
    //                     // case ServeAttstationDuty(attestation_duty) => 
    //                     //     var messagesToBeSent := f_serve_attestation_duty(s_node, attestation_duty).outputs.att_shares_sent;
    //                     //     assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent + 
    //                     //         getMessagesFromMessagesWithRecipient(messagesToBeSent);
    //                     //     lem_f_serve_attestation_duty_constants(s_node, attestation_duty, s'_node);
    //                     //     assert messagesToBeSent == {};
    //                     //     lem_inv_data_of_att_share_is_decided_value_helper2(s'.att_network.allMessagesSent, s.att_network.allMessagesSent, messagesToBeSent);
    //                     //     assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent;
                            
                                                                    
    //                     // case ReceivedAttestationShare(attestation_share) => 
    //                     //     var messagesToBeSent := f_listen_for_attestation_shares(s_node, attestation_share).outputs.att_shares_sent;
    //                     //     assert messagesToBeSent == {};                        
    //                     //     assert s'.att_network.allMessagesSent == 
    //                     //                 s.att_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent);
    //                     //     assert s'.att_network.allMessagesSent == 
    //                     //                 s.att_network.allMessagesSent + getMessagesFromMessagesWithRecipient({});                                              

    //                     // case ImportedNewBlock(block) => 
    //                     //     var s_node := f_add_block_to_bn(s_node, nodeEvent.block);
    //                     //     var messagesToBeSent := f_listen_for_new_imported_blocks(s_node, block).outputs.att_shares_sent;
    //                     //     assert s'.att_network.allMessagesSent == 
    //                     //                 s.att_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent);
    //                     //     lem_f_listen_for_new_imported_blocksd_unchanged_dvc_vars(s_node, block, s'_node);
    //                     //     assert messagesToBeSent == {};
    //                     //     lem_inv_data_of_att_share_is_decided_value_helper2(s'.att_network.allMessagesSent, s.att_network.allMessagesSent, messagesToBeSent);
    //                     //     assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent;                 
                    
    //                     // case ResendAttestationShares => 
    //                     //     var messagesToBeSent := f_resend_attestation_share(s_node).outputs.att_shares_sent;     

    //                     //     assert s'.att_network.allMessagesSent == 
    //                     //                 s.att_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent);  

    //                     //     forall m | m in getMessagesFromMessagesWithRecipient(messagesToBeSent)  
    //                     //     ensures m in s.att_network.allMessagesSent
    //                     //     {
    //                     //         assert m in s_node.attestation_shares_to_broadcast.Values;
    //                     //         assert m in s.att_network.allMessagesSent;
    //                     //     }        

    //                     //     assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent;

    //                     // case NoEvent => 
    //                     //     assert s'.att_network == s.att_network;
    //                 }
    //                 // lem_inv_data_of_att_share_is_decided_value_helper(s, event, s');
    //             }


    //         case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
    //         //     lem_inv_data_of_att_share_is_decided_value_att_adversary(s, event, s');
    //     }        
    // }

    lemma lem_inv_data_of_att_share_is_decided_value(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_quorum_constraints(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_data_of_att_share_is_decided_value(s)
    requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)      
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(s)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(s)          
    requires |s.all_nodes| > 0
    ensures inv_data_of_att_share_is_decided_value(s')   
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                if nodeEvent.AttConsensusDecided? 
                {
                    lem_inv_data_of_att_share_is_decided_value_att_consensus_decided(s, event, s');
                }
                else 
                {
                    match nodeEvent
                    {
                        case ServeAttstationDuty(attestation_duty) => 
                            var messagesToBeSent := f_serve_attestation_duty(s_node, attestation_duty).outputs.att_shares_sent;
                            assert s'.att_network.allMessagesSent == 
                                        s.att_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent);
                            lem_f_serve_attestation_duty_constants(s_node, attestation_duty, s'_node);
                            assert messagesToBeSent == {};
                            lem_inv_data_of_att_share_is_decided_value_helper2(s'.att_network.allMessagesSent, s.att_network.allMessagesSent, messagesToBeSent);
                            assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent;
                            
                                                                    
                        case ReceivedAttestationShare(attestation_share) => 
                            var messagesToBeSent := f_listen_for_attestation_shares(s_node, attestation_share).outputs.att_shares_sent;
                            assert messagesToBeSent == {};                        
                            assert s'.att_network.allMessagesSent == 
                                        s.att_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent);
                            assert s'.att_network.allMessagesSent == 
                                        s.att_network.allMessagesSent + getMessagesFromMessagesWithRecipient({});                                              

                        case ImportedNewBlock(block) => 
                            var s_node := f_add_block_to_bn(s_node, nodeEvent.block);
                            var messagesToBeSent := f_listen_for_new_imported_blocks(s_node, block).outputs.att_shares_sent;
                            assert s'.att_network.allMessagesSent == 
                                        s.att_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent);
                            lem_f_listen_for_new_imported_blocksd_unchanged_dvc_vars(s_node, block, s'_node);
                            assert messagesToBeSent == {};
                            lem_inv_data_of_att_share_is_decided_value_helper2(s'.att_network.allMessagesSent, s.att_network.allMessagesSent, messagesToBeSent);
                            assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent;                 
                    
                        case ResendAttestationShares => 
                            var messagesToBeSent := f_resend_attestation_share(s_node).outputs.att_shares_sent;     

                            assert s'.att_network.allMessagesSent == 
                                        s.att_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent);  

                            forall m | m in getMessagesFromMessagesWithRecipient(messagesToBeSent)  
                            ensures m in s.att_network.allMessagesSent
                            {
                                assert m in s_node.attestation_shares_to_broadcast.Values;
                                assert m in s.att_network.allMessagesSent;
                            }        

                            assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent;

                        case NoEvent => 
                            assert s'.att_network == s.att_network;
                    }
                    lem_inv_data_of_att_share_is_decided_value_helper(s, event, s');
                }

            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                lem_inv_data_of_att_share_is_decided_value_att_adversary(s, event, s');
        }        
    }
}