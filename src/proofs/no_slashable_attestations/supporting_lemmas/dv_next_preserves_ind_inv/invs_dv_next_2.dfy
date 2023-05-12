include "../../../../common/commons.dfy"
include "../../common/dvc_attestation_creation_instrumented.dfy"
include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_attestation_creation.dfy"
include "../../../../specs/dvc/dvc_attestation_creation.dfy"

include "../../../no_slashable_attestations/common/common_proofs.dfy"
include "../../../bn_axioms.dfy"
include "../../../rs_axioms.dfy"

include "invs_dv_next_1.dfy"
include "../inv.dfy"
include "../../../common/att_helper_pred_fcn.dfy"
include "../../../common/quorum_lemmas.dfy"


module Invs_Att_DV_Next_2
{
    import opened Types 
    import opened Common_Functions
    import opened Set_Seq_Helper
    import opened Signing_Methods
    import opened ConsensusSpec
    import opened Consensus_Engine_Instr
    import opened NetworkSpec
    import opened Att_DVC_Spec
    import opened Att_DV    
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Common_Proofs
    import opened Invs_Att_DV_Next_1
    import Att_DVC_Spec_NonInstr
    import opened BN_Axioms
    import opened RS_Axioms
    import opened Att_Helper_Pred_Fcn
    import opened Quorum_Lemmas

    predicate pred_the_latest_attestation_duty_was_sent_from_dv(
        s': Att_DVState,
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

    lemma lem_ServeAttestationDuty_constraints2_helper(
        s: Att_DVState,
        node: BLSPubkey,
        nodeEvent: Types.AttestationEvent,
        nodeOutputs: Att_DVC_Spec.Outputs,
        s': Att_DVState
    )
    requires NextHonestAfterAddingBlockToBn.requires(s, node, nodeEvent, nodeOutputs, s' );
    requires NextHonestAfterAddingBlockToBn(s, node, nodeEvent, nodeOutputs, s' );  
    requires nodeEvent.ServeAttestationDuty?
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
            case ServeAttestationDuty(attestation_duty) => 
                assert s.sequence_attestation_duties_to_be_served == s'.sequence_attestation_duties_to_be_served;
                assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;

                var an := s'.sequence_attestation_duties_to_be_served[s'.index_next_attestation_duty_to_be_served - 1];

                assert attestation_duty == an.attestation_duty;
                assert node == an.node;
        }
    }     

    lemma lem_ServeAttestationDuty_constraints(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')    
    requires event.HonestNodeTakingStep?
    requires event.event.ServeAttestationDuty?
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
                lem_ServeAttestationDuty_constraints2_helper(add_block_to_bn_with_event(s, node, nodeEvent), node, nodeEvent, nodeOutputs, s' );
        }        
    }    

    lemma lem_f_serve_attestation_duty_constants(
        s: Att_DVCState,
        attestation_duty: AttestationDuty,
        s': Att_DVCState
    )  
    requires f_serve_attestation_duty.requires(s, attestation_duty)
    requires s' == f_serve_attestation_duty(s, attestation_duty).state
    ensures s'.bn.submitted_data == s.bn.submitted_data      
    ensures s'.rcvd_attestation_shares == s.rcvd_attestation_shares
    ensures f_serve_attestation_duty(s, attestation_duty).outputs == getEmptyOuputs()
    { }

    lemma lem_f_check_for_next_duty_unchanged_dvc_vars(
        s: Att_DVCState,
        attestation_duty: AttestationDuty,
        s': Att_DVCState
    )
    requires f_check_for_next_duty.requires(s, attestation_duty)
    requires s' == f_check_for_next_duty(s, attestation_duty).state
    ensures s'.bn.submitted_data == s.bn.submitted_data
    ensures s'.rcvd_attestation_shares == s.rcvd_attestation_shares
    ensures f_check_for_next_duty(s, attestation_duty).outputs == getEmptyOuputs()
    { }

    lemma lem_f_att_consensus_decided_unchanged_dvc_vars(
        s: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': Att_DVCState
    )
    requires f_att_consensus_decided.requires(s, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(s, id, decided_attestation_data).state
    ensures s'.bn.submitted_data == s.bn.submitted_data
    ensures s'.rcvd_attestation_shares == s.rcvd_attestation_shares
    { } 

    lemma lem_f_listen_for_new_imported_blocks_unchanged_dvc_vars(
        s: Att_DVCState,
        block: BeaconBlock,
        s': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(s, block)
    requires s' == f_listen_for_new_imported_blocks(s, block).state
    ensures s'.bn.submitted_data == s.bn.submitted_data
    ensures s'.rcvd_attestation_shares.Keys <= s.rcvd_attestation_shares.Keys
    ensures forall k | k in s'.rcvd_attestation_shares.Keys :: s'.rcvd_attestation_shares[k] == s.rcvd_attestation_shares[k]
    ensures f_listen_for_new_imported_blocks(s, block).outputs == getEmptyOuputs()
    { }  

    lemma lem_f_listen_for_attestation_shares_unchanged_dvc_vars(
        s: Att_DVCState,
        attestation_share: AttestationShare,
        s': Att_DVCState
    )
    requires f_listen_for_attestation_shares.requires(s, attestation_share)
    requires s' == f_listen_for_attestation_shares(s, attestation_share).state    
    ensures s'.attestation_consensus_engine_state == s.attestation_consensus_engine_state
    ensures s'.attestation_consensus_engine_state.slashing_db_hist == s.attestation_consensus_engine_state.slashing_db_hist
    ensures s'.latest_attestation_duty == s.latest_attestation_duty
    ensures s'.current_attestation_duty == s.current_attestation_duty
    ensures s'.attestation_slashing_db == s.attestation_slashing_db
    ensures s'.future_att_consensus_instances_already_decided == s.future_att_consensus_instances_already_decided
    { }

    lemma lem_f_resend_attestation_share_unchanged_dvc_vars(
        s: Att_DVCState,
        s': Att_DVCState
    )
    requires f_resend_attestation_share.requires(s)
    requires s' == f_resend_attestation_share(s).state    
    ensures s'.attestation_consensus_engine_state == s.attestation_consensus_engine_state
    ensures s'.attestation_consensus_engine_state.slashing_db_hist == s.attestation_consensus_engine_state.slashing_db_hist
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

    lemma lem_inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_ex_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        s': Att_DVCState,
        dv: Att_DVState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires s' == f_listen_for_attestation_shares(process, attestation_share).state
    requires construct_signed_attestation_signature_assumptions_helper(
        process.construct_signed_attestation_signature,
        process.dv_pubkey,
        dv.all_nodes
    )
    requires inv_all_honest_nodes_is_a_quorum(dv)
    requires attestation_share in dv.att_network.allMessagesSent
    requires inv_rcvd_attestation_shares_are_sent_messages_body(dv, process)
    ensures forall a | a in f_listen_for_attestation_shares(process, attestation_share).outputs.submitted_data ::
                        exists hn', att_share: AttestationShare :: inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_body(dv, hn', att_share, a);
    {
        var activate_att_consensus_intances := process.attestation_consensus_engine_state.active_consensus_instances.Keys;

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
        
                assert inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_body(
                                dv,
                                h_s,
                                h_s_att,
                                aggregated_attestation
                            );

                assert f_listen_for_attestation_shares(process, attestation_share).outputs.submitted_data == {aggregated_attestation};

                assert forall a | a in f_listen_for_attestation_shares(process, attestation_share).outputs.submitted_data ::
                            exists hn', att_share: AttestationShare :: inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_body(dv, hn', att_share, a);
            }
        }   
    }    

    lemma lem_inv_rcvd_attestation_shares_are_sent_messages_f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare,
        s': Att_DVCState,
        dv: Att_DVState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires s' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv_rcvd_attestation_shares_are_sent_messages_body(dv, process)
    requires attestation_share in dv.att_network.allMessagesSent
    ensures inv_rcvd_attestation_shares_are_sent_messages_body(dv, s') 
    { }    

    lemma lem_inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_ex_helper(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(s)
    requires s'.all_attestations_created == s.all_attestations_created
    ensures inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(s');
    {
        forall a |
            && a in s'.all_attestations_created
            && is_valid_attestation(a, s'.dv_pubkey)
        ensures exists hn', att_share: AttestationShare :: inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_body(s', hn', att_share, a);
        {
            var hn', att_share: AttestationShare :|
                inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_body(s, hn', att_share, a);
            
            assert inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_body(s', hn', att_share, a);
            assert exists hn', att_share: AttestationShare :: inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_body(s', hn', att_share, a);
        }
    }    

    lemma lem_inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_dv_next_ReceivedAttestationShare(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event.event.ReceivedAttestationShare?
    requires inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(s)
    requires construct_signed_attestation_signature_assumptions_helper(
        s.construct_signed_attestation_signature,
        s.dv_pubkey,
        s.all_nodes
    )
    requires inv_only_dv_construct_signed_attestation_signature(s)  
    requires inv_in_transit_messages_are_in_allMessagesSent(s)
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_rcvd_attestation_shares_are_sent_messages(s)    
    ensures inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(s')
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ReceivedAttestationShare(attestation_share) => 
                        assert multiset(addReceipientToMessages<AttestationShare>({attestation_share}, node)) <= s.att_network.messagesInTransit;

                        assert MessaageWithRecipient(message := attestation_share, receipient := node) in s.att_network.messagesInTransit;      

                        var stateAndOutput := f_listen_for_attestation_shares(s_node, attestation_share);  

                        
                        assert attestation_share in s.att_network.allMessagesSent;
                        assert s'.all_attestations_created == s.all_attestations_created + stateAndOutput.outputs.submitted_data;

                        lem_inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_ex_f_listen_for_attestation_shares(
                            s_node,
                            attestation_share,
                            s'_node,
                            s
                        );

                        forall a | 
                                    && a in s'.all_attestations_created
                                    && is_valid_attestation(a, s'.dv_pubkey)
                        ensures exists hn', att_share: AttestationShare :: inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_body(s', hn', att_share, a);            
                        {
                            if a in s.all_attestations_created
                            {
                                var hn', att_share: AttestationShare :| inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_body(s, hn', att_share, a);
                                assert inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_body(s', hn', att_share, a);
                            }
                            else 
                            {
                                assert a in stateAndOutput.outputs.submitted_data;
                                var hn', att_share: AttestationShare :| inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_body(s, hn', att_share, a);
                                assert inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_body(s', hn', att_share, a);
                            }                                   
                        }                                

                        assert inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(s');  
                }
        }
    }

    lemma lem_inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_dv_next_AdversaryTakingStep(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.AdversaryTakingStep?
    requires inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(s)
    requires construct_signed_attestation_signature_assumptions_helper(
        s.construct_signed_attestation_signature,
        s.dv_pubkey,
        s.all_nodes
    )
    requires inv_only_dv_construct_signed_attestation_signature(s)  
    requires inv_in_transit_messages_are_in_allMessagesSent(s)
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_rcvd_attestation_shares_are_sent_messages(s)    
    ensures inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(s')
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>    
                forall a | 
                    && a in s'.all_attestations_created
                    && is_valid_attestation(a, s'.dv_pubkey)
                ensures exists hn', att_share: AttestationShare :: inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_body(s', hn', att_share, a);      
                {
                    if a in s.all_attestations_created
                    {
                        var hn', att_share: AttestationShare :| inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_body(s, hn', att_share, a);
                        assert inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_body(s', hn', att_share, a);                        
                    }
                    else 
                    {
                        var attestation_shares :| 
                            && attestation_shares <= s'.att_network.allMessagesSent
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

                        assert inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_body(
                            s,
                            h_s,
                            h_s_att,
                            a
                        );      

                        assert inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_body(
                            s',
                            h_s,
                            h_s_att,
                            a
                        );                                                                                                                                                 
                    }
                }
                assert inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(s');
        }
    }

    lemma lem_inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_dv_next(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(s)
    requires construct_signed_attestation_signature_assumptions_helper(
        s.construct_signed_attestation_signature,
        s.dv_pubkey,
        s.all_nodes
    )
    requires inv_only_dv_construct_signed_attestation_signature(s)  
    requires inv_in_transit_messages_are_in_allMessagesSent(s)
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_rcvd_attestation_shares_are_sent_messages(s)    
    ensures inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(s')
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) => 
                        lem_inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_ex_helper(s, event, s');
                        assert inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(s');  

                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_f_att_consensus_decided_unchanged_dvc_vars(s.honest_nodes_states[node], id, decided_attestation_data, s'.honest_nodes_states[node]);
                        lem_inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_ex_helper(s, event, s');
                        assert inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(s');            

                    case ReceivedAttestationShare(attestation_share) => 
                        lem_inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_dv_next_ReceivedAttestationShare(
                            s,
                            event,
                            s'
                        );

                    case ImportedNewBlock(block) => 
                        var s_node := f_add_block_to_bn(s_node, nodeEvent.block);
                        lem_f_listen_for_new_imported_blocks_unchanged_dvc_vars(s_node, block, s'_node);
                        assert s'.all_attestations_created == s.all_attestations_created;
                        lem_inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_ex_helper(s, event, s');
                        assert inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(s');     

                    case ResendAttestationShares => 
                        assert s'.all_attestations_created == s.all_attestations_created;
                        lem_inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_ex_helper(s, event, s');
                        assert inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(s');

                    case NoEvent => 
                        assert s'.all_attestations_created == s.all_attestations_created;
                        lem_inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_ex_helper(s, event, s');
                        assert inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(s');
                }

            case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                lem_inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_dv_next_AdversaryTakingStep(
                    s,
                    event,
                    s'
                );
        }
    }        

    lemma lem_inv_rcvd_attestation_shares_are_sent_messages(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_in_transit_messages_are_in_allMessagesSent(s)
    requires inv_rcvd_attestation_shares_are_sent_messages(s)
    ensures inv_rcvd_attestation_shares_are_sent_messages(s')
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) => 
                        lem_f_serve_attestation_duty_constants(s_node, attestation_duty, s'_node);

                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_f_att_consensus_decided_unchanged_dvc_vars(s_node, id, decided_attestation_data, s'_node);

                    case ReceivedAttestationShare(attestation_share) => 
                        assert multiset(addReceipientToMessages<AttestationShare>({attestation_share}, node)) <= s.att_network.messagesInTransit;
                        assert MessaageWithRecipient(message := attestation_share, receipient := node) in s.att_network.messagesInTransit;        
                        assert attestation_share in s.att_network.allMessagesSent;                    
                        lem_inv_rcvd_attestation_shares_are_sent_messages_f_listen_for_attestation_shares(
                            s_node,
                            attestation_share,
                            s'_node,
                            s
                        );

                    case ImportedNewBlock(block) => 
                        var s_node := f_add_block_to_bn(s_node, nodeEvent.block);
                        lem_f_listen_for_new_imported_blocks_unchanged_dvc_vars(s_node, block, s'_node);
                        assert inv_rcvd_attestation_shares_are_sent_messages(s');      

                    case ResendAttestationShares => 
                        assert inv_rcvd_attestation_shares_are_sent_messages(s');                    
                    case NoEvent => 

                }

            case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>

        }
    }     

    lemma lem_getMessagesFromEmptySetOfMessagesWithRecipient_is_empty_set<M>(mswr: set<MessaageWithRecipient<M>>)
    requires mswr == {}
    ensures getMessagesFromMessagesWithRecipient(mswr) == {}
    {
    }

    lemma lem_inv_data_of_att_shares_are_decided_values_helper(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_data_of_att_shares_are_decided_values(s)
    requires inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s)
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires |s.all_nodes| > 0
    requires s'.att_network.allMessagesSent == 
                    s.att_network.allMessagesSent + getMessagesFromMessagesWithRecipient({});
    ensures  inv_data_of_att_shares_are_decided_values(s');
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
        ensures inv_data_of_att_shares_are_decided_values_body(s', att_share);
        {
            assert att_share in s.att_network.allMessagesSent;
            assert inv_data_of_att_shares_are_decided_values_body(s, att_share);
            assert inv_data_of_att_shares_are_decided_values_body(s', att_share);
        }

        assert inv_data_of_att_shares_are_decided_values(s');   
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

    lemma lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_get_s_w_honest_node_states_updated(
        s: Att_DVState,
        node: BLSPubkey,
        nodeEvent: Types.AttestationEvent
    ) returns (s_w_honest_node_states_updated: Att_DVState)
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

    lemma lem_inv_data_of_att_shares_are_decided_values_att_consensus_decided_helper_2(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event.event.AttConsensusDecided?
    requires inv_all_honest_nodes_is_a_quorum(s)
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
                        var s_w_honest_node_states_updated := lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_get_s_w_honest_node_states_updated(s, node, nodeEvent);           
                        var cid := id;

                        assert s_w_honest_node_states_updated.consensus_on_attestation_data == s.consensus_on_attestation_data;

                        var output := Some(Decided(node, nodeEvent.decided_attestation_data)); 

                        var validityPredicates := 
                                map n |
                                        && n in s_w_honest_node_states_updated.honest_nodes_states.Keys 
                                        && cid in s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_consensus_instances.Keys
                                    ::
                                        s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_consensus_instances[cid].validityPredicate
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

    lemma lem_inv_monotonic_allMessagesSent(
        dv: Att_DVState,
        event: Att_DV.AttestationEvent,
        dv': Att_DVState
    )       
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    ensures dv.att_network.allMessagesSent <= dv'.att_network.allMessagesSent
    {}

    lemma lem_inv_decided_values_of_consensus_instances_are_decided_by_a_quorum_helper(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        cid: Slot,
        s': Att_DVState,
        node: BLSPubkey, 
        nodeEvent: Types.AttestationEvent, 
        nodeOutputs: Outputs
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires cid in s'.consensus_on_attestation_data.Keys
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)    
    requires s.consensus_on_attestation_data[cid].decided_value.isPresent()
    ensures is_a_valid_decided_value(s'.consensus_on_attestation_data[cid]); 
    {
        lem_inv_monotonic_allMessagesSent(s, event, s');
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;

        
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
                    && cid in s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_consensus_instances.Keys
                ::
                    s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_consensus_instances[cid].validityPredicate
            ;

        var s_consensus := s_w_honest_node_states_updated.consensus_on_attestation_data[cid];
        var s'_consensus := s'.consensus_on_attestation_data[cid];                

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

    lemma lem_inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)    
    ensures inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s')   
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

                forall cid | && cid in s'.consensus_on_attestation_data.Keys
                             && s'.consensus_on_attestation_data[cid].decided_value.isPresent()
                ensures is_a_valid_decided_value(s'.consensus_on_attestation_data[cid]);
                {
                    if s.consensus_on_attestation_data[cid].decided_value.isPresent()
                    {
                        lem_inv_decided_values_of_consensus_instances_are_decided_by_a_quorum_helper(s, event, cid, s', node, nodeEvent, nodeOutputs);
                    }
                    else
                    {
                        assert is_a_valid_decided_value(s'.consensus_on_attestation_data[cid]);
                    }
                }
                assert inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s');
               

            case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                assert inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s');
        }        
    } 

    lemma lem_inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k_helper(
        s: Att_DVState,
        cid: Slot
    )
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)    
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(s)
    requires inv_all_honest_nodes_is_a_quorum(s)
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
                inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_body(cid, attestation_duty, attestation_slashing_db, vp);

        assert s_consensus.decided_value.safe_get().slot == cid;
    }

    lemma lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_get_s_w_honest_node_states_updated_2(
        s: Att_DVState,
        node: BLSPubkey,
        nodeEvent: Types.AttestationEvent,
        node': BLSPubkey,
        s_w_honest_node_states_updated: Att_DVState
    ) 
    requires node in s.honest_nodes_states.Keys
    requires node' in s.honest_nodes_states.Keys
    requires s_w_honest_node_states_updated == add_block_to_bn_with_event(s, node, nodeEvent)
    ensures s_w_honest_node_states_updated.honest_nodes_states[node'].attestation_consensus_engine_state == s.honest_nodes_states[node'].attestation_consensus_engine_state
    {      
    }  

    lemma lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_helper(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState,
        cid: Slot,
        hn: BLSPubkey,
        vp: AttestationData -> bool
    )   returns (attestation_duty: AttestationDuty, attestation_slashing_db: set<SlashingDBAttestation>)
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')    
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)      
    requires
            && hn in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions.Keys
            && vp in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions[hn]
    requires event.HonestNodeTakingStep?
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(s)
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s)
    ensures inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_body(cid, attestation_duty, attestation_slashing_db, vp); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];

                var s_w_honest_node_states_updated :=
                    lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_get_s_w_honest_node_states_updated(s, node, nodeEvent);         

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
                            && cid in s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_consensus_instances.Keys
                        ::
                            s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_consensus_instances[cid].validityPredicate
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

                attestation_duty, attestation_slashing_db :| inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_body(cid, attestation_duty, attestation_slashing_db, vp);

            }
            else 
            {
                assert vp in validityPredicates.Values;
                var vpn :| vpn in validityPredicates.Keys && validityPredicates[vpn] == vp;
                assert validityPredicates[vpn] == s_w_honest_node_states_updated.honest_nodes_states[vpn].attestation_consensus_engine_state.active_consensus_instances[cid].validityPredicate;

                assert vpn in s.honest_nodes_states.Keys;
                assert cid in s_w_honest_node_states_updated.honest_nodes_states[vpn].attestation_consensus_engine_state.active_consensus_instances.Keys;

                lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_get_s_w_honest_node_states_updated_2(s, node, nodeEvent, vpn, s_w_honest_node_states_updated);

                assert s_w_honest_node_states_updated.honest_nodes_states[vpn].attestation_consensus_engine_state == s.honest_nodes_states[vpn].attestation_consensus_engine_state;
                assert inv_every_active_consensus_instance_has_a_corresponding_att_duty_and_a_validity_predicate(s, vpn, cid);

                attestation_duty, attestation_slashing_db :| inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_body(cid, attestation_duty, attestation_slashing_db, vp);
            }

            assert inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_body(cid, attestation_duty, attestation_slashing_db, vp);
        }

    }  

    lemma lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )   
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')    
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(s)
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)      
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s)  
    ensures inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(s')   
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                forall hn, cid: Slot, vp |
                    && hn in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions.Keys
                    && vp in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions[hn]
                ensures exists attestation_duty, attestation_slashing_db :: inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_body(cid, attestation_duty, attestation_slashing_db, vp)
                {
                    var attestation_duty: AttestationDuty, attestation_slashing_db := lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_helper(s, event, s', cid, hn, vp);
                }
                assert inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(s');

            case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                assert inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(s');
        }
    }   

    lemma lem_inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)    
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(s)
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s)  
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)  
    ensures inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s') 
    {
        lem_inv_all_honest_nodes_is_a_quorum_dv_next(s, event, s');
        lem_inv_unchanged_paras_of_consensus_instances_dv_next(s, event, s');
        lem_inv_only_dv_construct_signed_attestation_signature_dv_next(s, event, s');
        lem_inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s, event, s');
        lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(s, event, s');
        lem_inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k2(s');   
    }     

    lemma lem_inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k2(
        s: Att_DVState
    )
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)    
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(s)
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    ensures inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s) 
    {
        forall cid |
            && cid in s.consensus_on_attestation_data.Keys
            && s.consensus_on_attestation_data[cid].decided_value.isPresent()
        {
           lem_inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k_helper(s, cid);
        }        
    }       

    lemma lemmaImaptotalElementInDomainIsInKeys<K(!new), V>(m: imaptotal<K, V>, e: K)
    ensures e in m.Keys
    { }

    lemma lemmaOnGetMessagesFromMessagesWithRecipientWhenAllMessagesAreTheSame<M>(
        messagesToBeSent: set<MessaageWithRecipient<M>>,
        message: M
    )
    requires forall m | m in messagesToBeSent :: m.message == message 
    requires messagesToBeSent != {}
    ensures getMessagesFromMessagesWithRecipient(messagesToBeSent) ==  {message}
    { }

    lemma lem_inv_data_of_att_shares_are_decided_values_att_consensus_decided_with_decided_data_for_current_slot(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState,
        node: BLSPubkey, 
        nodeEvent: Types.AttestationEvent, 
        nodeOutputs: Outputs,
        id: Slot, 
        decided_attestation_data: AttestationData
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires nodeEvent.AttConsensusDecided?
    requires nodeEvent == AttConsensusDecided(id, decided_attestation_data)
    requires inv_data_of_att_shares_are_decided_values(s)
    requires inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)  
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)    
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(s)
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s)          
    requires |s.all_nodes| > 0
    requires && var process := s.honest_nodes_states[node];
             && is_decided_data_for_current_slot(process, decided_attestation_data, id)
    ensures inv_data_of_att_shares_are_decided_values(s')   
    {
        var process := s.honest_nodes_states[node];
        var process' := s'.honest_nodes_states[node];

        var attestation_with_signature_share := 
            f_calc_att_with_sign_share_from_decided_att_data(
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
            if att_share in s.att_network.allMessagesSent
            {
                lem_inv_data_of_att_shares_are_decided_values_att_consensus_decided_helper_1(s, event, s', hn, att_share);    
            }
            else
            {
                assert att_share == attestation_with_signature_share;
                lemmaImaptotalElementInDomainIsInKeys(s.consensus_on_attestation_data, id);
                assert id in s.consensus_on_attestation_data.Keys ;
                lem_inv_data_of_att_shares_are_decided_values_att_consensus_decided_helper_2(s, event, s');

                assert s'.consensus_on_attestation_data[id].decided_value.safe_get() == decided_attestation_data; 
                assert s'.consensus_on_attestation_data[id].decided_value.safe_get() == att_share.data; 
                lem_inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s, event, s');   
                
                assert att_share.data.slot == id;
                assert s'.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent();                             
                assert s'.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data; 
            } 
        }           

        assert inv_data_of_att_shares_are_decided_values(s');
    }

    lemma lem_inv_data_of_att_shares_are_decided_values_att_consensus_decided_without_decided_data_for_current_slot(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState,
        node: BLSPubkey, 
        nodeEvent: Types.AttestationEvent, 
        nodeOutputs: Outputs,
        id: Slot, 
        decided_attestation_data: AttestationData
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires nodeEvent.AttConsensusDecided?
    requires nodeEvent == AttConsensusDecided(id, decided_attestation_data)
    requires inv_data_of_att_shares_are_decided_values(s)
    requires inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)  
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)    
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(s)
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s)          
    requires |s.all_nodes| > 0
    requires && var process := s.honest_nodes_states[node];
             && !is_decided_data_for_current_slot(process, decided_attestation_data, id)
    ensures inv_data_of_att_shares_are_decided_values(s')   
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
            lem_inv_data_of_att_shares_are_decided_values_att_consensus_decided_helper_1(s, event, s', hn, att_share);
        } 

        assert inv_data_of_att_shares_are_decided_values(s');
    }

    lemma lem_inv_data_of_att_shares_are_decided_values_att_consensus_decided(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event.event.AttConsensusDecided?
    requires inv_data_of_att_shares_are_decided_values(s)
    requires inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)  
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)    
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(s)
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s)          
    requires |s.all_nodes| > 0
    ensures inv_data_of_att_shares_are_decided_values(s')   
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
                            lem_inv_data_of_att_shares_are_decided_values_att_consensus_decided_with_decided_data_for_current_slot(
                                s,
                                event,
                                s',
                                node, 
                                nodeEvent, 
                                nodeOutputs,
                                id, 
                                decided_attestation_data
                            );                            
                        }
                        else 
                        {
                            lem_inv_data_of_att_shares_are_decided_values_att_consensus_decided_without_decided_data_for_current_slot(
                                s,
                                event,
                                s',
                                node, 
                                nodeEvent, 
                                nodeOutputs,
                                id, 
                                decided_attestation_data
                            );                            
                        }
                }
        }
    }

    lemma lem_inv_data_of_att_shares_are_decided_values_att_adversary(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.AdversaryTakingStep?
    requires inv_data_of_att_shares_are_decided_values(s)
    requires inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)  
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires |s.all_nodes| > 0
    ensures inv_data_of_att_shares_are_decided_values(s') 
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
    
        assert inv_data_of_att_shares_are_decided_values(s');
    }      

    lemma lem_inv_data_of_att_shares_are_decided_values_helper2<M>(
        allMessagesSent': set<M>,
        allMessagesSent: set<M>,
        messagesToBeSent: set<MessaageWithRecipient<M>>
    )
    requires allMessagesSent' == allMessagesSent + 
                                getMessagesFromMessagesWithRecipient(messagesToBeSent);
    requires messagesToBeSent == {}
    ensures allMessagesSent' == allMessagesSent
    { }

       

    lemma lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dvc_updateAttConsensusInstanceValidityCheckHelper(
        m: map<Slot, AttestationConsensusValidityCheckState>,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        m': map<Slot, AttestationConsensusValidityCheckState>
    )    
    requires m' == updateAttConsensusInstanceValidityCheckHelper(m, new_attestation_slashing_db)
    requires forall k | k in m.Keys :: inv_existing_slashing_db_for_given_att_duty_and_vp(k, m[k].attestation_duty, m[k].validityPredicate)
    ensures forall k | k in m'.Keys :: inv_existing_slashing_db_for_given_att_duty_and_vp(k, m'[k].attestation_duty, m'[k].validityPredicate)    
    {
        forall k | k in  m.Keys
        ensures k in m'.Keys
        {
            lemmaMapKeysHasOneEntryInItems(m, k);
            assert k in m';
        }

        assert m.Keys == m'.Keys;

        forall k | k in m'.Keys
        ensures inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_body(k, m'[k].attestation_duty, new_attestation_slashing_db, m'[k].validityPredicate); 
        {
            assert m'[k] == m[k].(
                    validityPredicate := (ad: AttestationData) => ci_decision_is_valid_attestation_data(new_attestation_slashing_db, ad, m[k].attestation_duty)
            );
            assert  inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_body(k, m'[k].attestation_duty, new_attestation_slashing_db, m'[k].validityPredicate);        
        }
    }

    
    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_duty_updateAttConsensusInstanceValidityCheck(
        s: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>
    )    
    requires s' == updateAttConsensusInstanceValidityCheck(s, new_attestation_slashing_db)
    ensures s'.active_consensus_instances.Keys == s.active_consensus_instances.Keys
    ensures s'.slashing_db_hist.Keys == s.slashing_db_hist.Keys + s'.active_consensus_instances.Keys;
    {
        lem_updateAttConsensusInstanceValidityCheckHelper(s.active_consensus_instances, new_attestation_slashing_db, s'.active_consensus_instances);

        assert s'.slashing_db_hist.Keys == s.slashing_db_hist.Keys + s'.active_consensus_instances.Keys;

        assert forall slot, vp: AttestationData -> bool |
                    && slot in s.slashing_db_hist.Keys 
                    && vp in s.slashing_db_hist[slot].Keys
                    ::
                    && s.slashing_db_hist.Keys <= s'.slashing_db_hist.Keys
                    && s.slashing_db_hist[slot].Keys <= s'.slashing_db_hist[slot].Keys
                    && s.slashing_db_hist[slot][vp] <= s'.slashing_db_hist[slot][vp]
        ;

        assert forall slot |
                    && slot in s'.active_consensus_instances.Keys 
                    && slot in s.slashing_db_hist.Keys
                    && var vp := s'.active_consensus_instances[slot].validityPredicate;
                    && vp in s.slashing_db_hist[slot].Keys
                    ::
                    var vp := s'.active_consensus_instances[slot].validityPredicate;
                    s.slashing_db_hist[slot][vp] + {new_attestation_slashing_db} == s'.slashing_db_hist[slot][vp];      

        assert forall slot, vp: AttestationData -> bool |
                    && slot in s'.slashing_db_hist.Keys 
                    && slot !in s.slashing_db_hist.Keys 
                    && vp in s'.slashing_db_hist[slot].Keys
                    ::
                    && vp == s'.active_consensus_instances[slot].validityPredicate
        ;      

        assert forall slot, vp: AttestationData -> bool |
                    && slot in s.slashing_db_hist.Keys 
                    && vp in s'.slashing_db_hist[slot].Keys
                    && vp !in s.slashing_db_hist[slot].Keys
                    ::
                    && s'.slashing_db_hist[slot][vp] == {new_attestation_slashing_db}
        ;     
                   
    }   

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_duty_updateAttConsensusInstanceValidityCheck2(
        s: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>,
        slot: Slot,
        vp: AttestationData -> bool 
    )    
    requires s' == updateAttConsensusInstanceValidityCheck(s, new_attestation_slashing_db)
    requires 
                    && slot in s'.active_consensus_instances.Keys 
                    && slot in s.slashing_db_hist.Keys
                    && vp == s'.active_consensus_instances[slot].validityPredicate
                    && vp in s.slashing_db_hist[slot].Keys  
    ensures s.slashing_db_hist[slot][vp] + {new_attestation_slashing_db} == s'.slashing_db_hist[slot][vp];      
    {
        lem_updateAttConsensusInstanceValidityCheckHelper(s.active_consensus_instances, new_attestation_slashing_db, s'.active_consensus_instances);

        assert s'.slashing_db_hist.Keys == s.slashing_db_hist.Keys + s'.active_consensus_instances.Keys;                   
    }   

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_duty_updateAttConsensusInstanceValidityCheck3(
        s: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>,
        slot: Slot,
        vp: AttestationData -> bool 
    )    
    requires s' == updateAttConsensusInstanceValidityCheck(s, new_attestation_slashing_db)
    requires 
                    && slot in s'.active_consensus_instances.Keys 
                    && slot in s.slashing_db_hist.Keys
                    && vp != s'.active_consensus_instances[slot].validityPredicate
                    && vp in s.slashing_db_hist[slot].Keys  
    ensures s.slashing_db_hist[slot][vp] == s'.slashing_db_hist[slot][vp];      
    {
        lem_updateAttConsensusInstanceValidityCheckHelper(s.active_consensus_instances, new_attestation_slashing_db, s'.active_consensus_instances);

        assert s'.slashing_db_hist.Keys == s.slashing_db_hist.Keys + s'.active_consensus_instances.Keys;                   
    }      

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_duty_updateAttConsensusInstanceValidityCheck4(
        s: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>,
        slot: Slot,
        vp: AttestationData -> bool 
    )    
    requires s' == updateAttConsensusInstanceValidityCheck(s, new_attestation_slashing_db)
    requires 
                    && slot !in s'.active_consensus_instances.Keys 
                    && slot in s.slashing_db_hist.Keys
                    && vp in s.slashing_db_hist[slot].Keys  
    ensures s.slashing_db_hist[slot][vp] == s'.slashing_db_hist[slot][vp];      
    {
        lem_updateAttConsensusInstanceValidityCheckHelper(s.active_consensus_instances, new_attestation_slashing_db, s'.active_consensus_instances);

        assert s'.slashing_db_hist.Keys == s.slashing_db_hist.Keys + s'.active_consensus_instances.Keys;                   
    }   

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_duty_updateAttConsensusInstanceValidityCheck5(
        s: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>,
        slot: Slot    
    )    
    requires s' == updateAttConsensusInstanceValidityCheck(s, new_attestation_slashing_db)
    requires slot in s.slashing_db_hist.Keys
    ensures slot in s'.slashing_db_hist.Keys
    ensures s.slashing_db_hist[slot].Keys <= s'.slashing_db_hist[slot].Keys;      
    {
        lem_updateAttConsensusInstanceValidityCheckHelper(s.active_consensus_instances, new_attestation_slashing_db, s'.active_consensus_instances);

        assert s'.slashing_db_hist.Keys == s.slashing_db_hist.Keys + s'.active_consensus_instances.Keys;                   
    }    

    lemma lem_inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate_f_terminate_current_attestation_duty(
        process: Att_DVCState,
        process': Att_DVCState
    )
    requires f_terminate_current_attestation_duty.requires(process)
    requires process' == f_terminate_current_attestation_duty(process)
    requires inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate(process)
    ensures inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate(process')
    { }       

    lemma lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dvc_f_start_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_start_next_duty(process, attestation_duty).state   
    requires inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate(process) 
    ensures inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate(process')
    {
        var new_process := f_new_process_after_starting_new_att_duty(process, attestation_duty);

        assert { attestation_duty.slot } ==
                     new_process.attestation_consensus_engine_state.active_consensus_instances.Keys - 
                            process.attestation_consensus_engine_state.active_consensus_instances.Keys;

        forall cid | cid in new_process.attestation_consensus_engine_state.active_consensus_instances.Keys
        ensures inv_exist_an_att_duty_and_a_validity_predicate_for_an_active_consensus_instance_at_slot_cid(new_process, cid) 
        { 
            if cid in process.attestation_consensus_engine_state.active_consensus_instances.Keys
            {
                assert inv_exist_an_att_duty_and_a_validity_predicate_for_an_active_consensus_instance_at_slot_cid(new_process, cid);
            }
            else
            {
                assert cid == attestation_duty.slot;
                
                var acvc := AttestationConsensusValidityCheckState(
                    attestation_duty := attestation_duty,
                    validityPredicate := (ad: AttestationData) => ci_decision_is_valid_attestation_data(process.attestation_slashing_db, ad, attestation_duty)
                );

                assert acvc == process'.attestation_consensus_engine_state.active_consensus_instances[cid];
                assert inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_body(cid, attestation_duty, process.attestation_slashing_db, acvc.validityPredicate);    
                assert inv_existing_slashing_db_for_given_att_duty_and_vp(cid, attestation_duty, acvc.validityPredicate);
                assert inv_exist_an_att_duty_and_a_validity_predicate_for_an_active_consensus_instance_at_slot_cid(new_process, cid);
            }
        }
    }
    
    lemma lem_inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate_f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires process' == f_check_for_next_duty(process, attestation_duty).state   
    requires inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate(process) 
    ensures inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate(process'); 
    {
        if pred_decision_of_att_duty_was_known(process, attestation_duty)
        {                
            var new_process := f_new_process_after_updateAttConsensusInstanceValidityCheck(process, attestation_duty);

            lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dvc_updateAttConsensusInstanceValidityCheckHelper(
                    process.attestation_consensus_engine_state.active_consensus_instances,
                    new_process.attestation_slashing_db,
                    new_process.attestation_consensus_engine_state.active_consensus_instances
            );
        }
        else 
        {
            lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dvc_f_start_next_duty(
                process,
                attestation_duty,
                process'
            );                
        }    
    }        

    lemma lem_inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate_f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty,
        process': Att_DVCState
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state  
    requires inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate(process) 
    ensures inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate(process'); 
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        lem_inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate_f_terminate_current_attestation_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate_f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty,
            process'
        );        
    }        

    lemma lem_inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate_f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': Att_DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(process, id, decided_attestation_data).state
    requires inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate(process) 
    ensures inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate(s'); 
    {
        if  is_decided_data_for_current_slot(process, decided_attestation_data, id)
        {
            var s_mod := f_update_process_after_att_duty_decided(
                            process,
                            id,
                            decided_attestation_data);

            lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dvc_updateAttConsensusInstanceValidityCheckHelper(
                    process.attestation_consensus_engine_state.active_consensus_instances,
                    s_mod.attestation_slashing_db,
                    s_mod.attestation_consensus_engine_state.active_consensus_instances
            );            
        }            
    }     

    lemma lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_f_listen_for_new_imported_blocks(
        process: Att_DVCState,
        block: BeaconBlock,
        s': Att_DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate(process) 
    ensures inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate(s');     
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var process := f_stopAttConsensusInstances_after_receiving_new_imported_blocks(
                                process,
                                block
                            );

        if pred_listen_for_new_imported_blocks_checker(process, att_consensus_instances_already_decided)
        {
            var s_mod := f_updateAttConsensusInstanceValidityCheck_in_listen_for_new_imported_blocks(
                                    process,
                                    att_consensus_instances_already_decided
                                );

            lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dvc_updateAttConsensusInstanceValidityCheckHelper(
                    process.attestation_consensus_engine_state.active_consensus_instances,
                    s_mod.attestation_slashing_db,
                    s_mod.attestation_consensus_engine_state.active_consensus_instances
            );            
        }
    }      

    lemma lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv_next_ServeAttestationDuty(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )   
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event.event.ServeAttestationDuty?  
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)      
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s)  
    ensures inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s')    
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) => 
                        forall n | n in s'.honest_nodes_states.Keys
                        ensures inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate(s'.honest_nodes_states[n]); 
                        {
                            if n == node
                            {
                                lem_inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate_f_serve_attestation_duty(s_node, attestation_duty, s'_node);
                                assert inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate(s'_node); 
                            }
                        }
                        assert inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s');                        
                }
        }          
    }

    lemma lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv_next_AttConsensusDecided(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )   
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event.event.AttConsensusDecided?  
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)      
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s)  
    ensures inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s')    
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        forall n | n in s'.honest_nodes_states.Keys
                        ensures inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate(s'.honest_nodes_states[n]); 
                        {
                            if n == node
                            {
                                lem_inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate_f_att_consensus_decided(s_node, id, decided_attestation_data, s'_node);
                                assert inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate(s'_node); 
                            }
                        }
                        assert inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s');    
                }
        }
    }

    lemma lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv_next_ReceivedAttestationShare(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )   
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event.event.ReceivedAttestationShare?  
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)      
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s)  
    ensures inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s')    
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ReceivedAttestationShare(attestation_share) => 
                        forall n | n in s'.honest_nodes_states.Keys
                        ensures s'.honest_nodes_states[n].attestation_consensus_engine_state == s.honest_nodes_states[n].attestation_consensus_engine_state
                        {
                            if n == node
                            {
                                lem_f_listen_for_attestation_shares_unchanged_dvc_vars(s_node, attestation_share, s'_node);
                            }
                        }
                        assert inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s');  
                }
        }
    }

    lemma lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv_next_ImportedNewBlock(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )   
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event.event.ImportedNewBlock?  
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)      
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s)  
    ensures inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s')    
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ImportedNewBlock(block) => 
                        forall n | n in s'.honest_nodes_states.Keys
                        ensures inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate(s'.honest_nodes_states[n]); 
                        {
                            if n == node
                            {
                                var s_node := f_add_block_to_bn(s_node, nodeEvent.block);
                                lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_f_listen_for_new_imported_blocks(s_node, block, s'_node);
                                assert inv_every_active_consensus_instance_of_dvc_has_a_corresponding_att_duty_and_a_validity_predicate(s'_node); 
                            }
                        }
                        assert inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s');          
                }
        }
    }

    lemma lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv_next(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )   
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')    
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)      
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s)  
    ensures inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s')    
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) => 
                        lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv_next_ServeAttestationDuty(
                            s,
                            event,
                            s'
                        );  

                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv_next_AttConsensusDecided(
                            s,
                            event,
                            s'
                        );  
                                           
              
                    case ReceivedAttestationShare(attestation_share) => 
                        lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv_next_ReceivedAttestationShare(
                            s,
                            event,
                            s'
                        );    

                    case ImportedNewBlock(block) => 
                        lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv_next_ImportedNewBlock(
                            s,
                            event,
                            s'
                        );                        
               
                    case ResendAttestationShares => 
                        assert inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s');
                   
                    case NoEvent => 
                        assert inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s');
                }            

            case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                assert inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s');
        }        
    } 

    lemma lem_f_listen_for_new_imported_blocks_helper_1(
        dv: Att_DVState,
        process: Att_DVCState,
        block: BeaconBlock,
        new_consensus_instances_already_decided: map<Slot, AttestationData>
    )
    requires f_listen_for_new_imported_blocks_helper_1.requires(process, block)
    requires new_consensus_instances_already_decided == f_listen_for_new_imported_blocks_helper_1(process, block)
    requires inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(dv)
    requires inv_data_of_att_shares_are_decided_values(dv)
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
                && Att_DVC_Spec_NonInstr.isMyAttestation(a, process.bn, block, valIndex)
                && a.data == new_consensus_instances_already_decided[slot]
            ;

            var a' :|
                && a' in dv.all_attestations_created
                && a'.data == a.data 
                && is_valid_attestation(a', dv.dv_pubkey);    

            var hn', att_share: AttestationShare :| inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_body(dv, hn', att_share, a');

            assert
            && dv.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent()
            && dv.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;

            assert
            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
            && dv.consensus_on_attestation_data[slot].decided_value.safe_get() == new_consensus_instances_already_decided[slot]
            ;              
        }
    }  

    lemma lem_inv_data_of_att_shares_are_decided_values_att_consensus_decided_helper_1(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState,
        hn: BLSPubkey,
        att_share: AttestationShare
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event.event.AttConsensusDecided?
    requires inv_data_of_att_shares_are_decided_values(s)
    requires inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)  
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)    
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(s)
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s)          
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
                        assert inv_data_of_att_shares_are_decided_values(s);
                        assert inv_data_of_att_shares_are_decided_values_body(s, att_share);
                        assert s.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent();
                        assert s.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;   

                        var s_w_honest_node_states_updated := lem_inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_get_s_w_honest_node_states_updated(s, node, nodeEvent);           
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
                                    && cid in s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_consensus_instances.Keys
                                ::
                                    s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_consensus_instances[cid].validityPredicate
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

    lemma lem_inv_data_of_att_shares_are_decided_values_dv_next_ServeAttestationDuty(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event.event.ServeAttestationDuty?
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_data_of_att_shares_are_decided_values(s)
    requires inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)      
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)    
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(s)    
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s)          
    requires |s.all_nodes| > 0
    ensures inv_data_of_att_shares_are_decided_values(s')   
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) => 
                        var messagesToBeSent := f_serve_attestation_duty(s_node, attestation_duty).outputs.att_shares_sent;
                        assert s'.att_network.allMessagesSent == 
                                    s.att_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent);
                        lem_f_serve_attestation_duty_constants(s_node, attestation_duty, s'_node);
                        assert messagesToBeSent == {};
                        lem_inv_data_of_att_shares_are_decided_values_helper2(s'.att_network.allMessagesSent, s.att_network.allMessagesSent, messagesToBeSent);
                        assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent;
                        lem_inv_data_of_att_shares_are_decided_values_helper(s, event, s');
                }
        }
    }

    lemma lem_inv_data_of_att_shares_are_decided_values_dv_next_ReceivedAttestationShare(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event.event.ReceivedAttestationShare?
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_data_of_att_shares_are_decided_values(s)
    requires inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)      
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)    
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(s)    
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s)          
    requires |s.all_nodes| > 0
    ensures inv_data_of_att_shares_are_decided_values(s')   
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ReceivedAttestationShare(attestation_share) => 
                        var messagesToBeSent := f_listen_for_attestation_shares(s_node, attestation_share).outputs.att_shares_sent;
                            assert messagesToBeSent == {};                        
                            assert s'.att_network.allMessagesSent == 
                                        s.att_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent);
                            assert s'.att_network.allMessagesSent == 
                                        s.att_network.allMessagesSent + getMessagesFromMessagesWithRecipient({});  
                        lem_inv_data_of_att_shares_are_decided_values_helper(s, event, s');
                }
        }
    }

    lemma lem_inv_data_of_att_shares_are_decided_values_dv_next_ImportedNewBlock(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event.event.ImportedNewBlock?
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_data_of_att_shares_are_decided_values(s)
    requires inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)      
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)    
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(s)    
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s)          
    requires |s.all_nodes| > 0
    ensures inv_data_of_att_shares_are_decided_values(s')   
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
                            var messagesToBeSent := f_listen_for_new_imported_blocks(s_node, block).outputs.att_shares_sent;
                            assert s'.att_network.allMessagesSent == 
                                        s.att_network.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent);
                            lem_f_listen_for_new_imported_blocks_unchanged_dvc_vars(s_node, block, s'_node);
                            assert messagesToBeSent == {};
                            lem_inv_data_of_att_shares_are_decided_values_helper2(s'.att_network.allMessagesSent, s.att_network.allMessagesSent, messagesToBeSent);
                            assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent;                  
                        lem_inv_data_of_att_shares_are_decided_values_helper(s, event, s');
                }
        }
    }

    lemma lem_inv_data_of_att_shares_are_decided_values_dv_next_ResendAttestationShares(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event.event.ResendAttestationShares?
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_data_of_att_shares_are_decided_values(s)
    requires inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)      
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)    
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(s)    
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s)          
    requires |s.all_nodes| > 0
    ensures inv_data_of_att_shares_are_decided_values(s')   
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
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

                            assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent;lem_inv_data_of_att_shares_are_decided_values_helper(s, event, s');
                }
        }
    }

    lemma lem_inv_data_of_att_shares_are_decided_values_dv_next(
        s: Att_DVState,
        event: Att_DV.AttestationEvent,
        s': Att_DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_unchanged_paras_of_consensus_instances(s)
    requires same_honest_nodes_in_dv_and_ci(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_data_of_att_shares_are_decided_values(s)
    requires inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)      
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)    
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(s)    
    requires inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s)          
    requires |s.all_nodes| > 0
    ensures inv_data_of_att_shares_are_decided_values(s')   
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                if nodeEvent.AttConsensusDecided? 
                {
                    lem_inv_data_of_att_shares_are_decided_values_att_consensus_decided(s, event, s');
                }
                else 
                {
                    match nodeEvent
                    {
                        case ServeAttestationDuty(attestation_duty) => 
                            lem_inv_data_of_att_shares_are_decided_values_dv_next_ServeAttestationDuty(
                                s,
                                event,
                                s'
                            );    
                            
                                                                    
                        case ReceivedAttestationShare(attestation_share) => 
                            lem_inv_data_of_att_shares_are_decided_values_dv_next_ReceivedAttestationShare(
                                s,
                                event,
                                s'
                            );                                     

                        case ImportedNewBlock(block) => 
                            lem_inv_data_of_att_shares_are_decided_values_dv_next_ImportedNewBlock(
                                s,
                                event,
                                s'
                            );
                    
                        case ResendAttestationShares => 
                            lem_inv_data_of_att_shares_are_decided_values_dv_next_ResendAttestationShares(
                                s,
                                event,
                                s'
                            );

                        case NoEvent => 
                            assert s'.att_network == s.att_network;
                            lem_inv_data_of_att_shares_are_decided_values_helper(s, event, s');
                    }
                    
                }

            case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                lem_inv_data_of_att_shares_are_decided_values_att_adversary(s, event, s');
        }        
    }
}