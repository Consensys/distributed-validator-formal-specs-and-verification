include "../../../../common/commons.dfy"
include "invs_fnc_1.dfy"
include "invs_fnc_2.dfy"

include "../../common/dvc_block_proposer_instrumented.dfy"
include "../../../bn_axioms.dfy"
include "../../../rs_axioms.dfy"

include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_block_proposer.dfy"
include "../inv.dfy"


include "../../common/common_proofs.dfy"

include "invs_dv_next_1.dfy"
include "invs_dv_next_2.dfy"
include "invs_dv_next_3.dfy"
include "invs_dv_next_4.dfy"

module Invs_DV_Next_5
{
    import opened Types
    import opened Set_Seq_Helper
    import opened Signing_Methods
    import opened Common_Functions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Block_Proposer_Spec_Instr
    import opened Consensus_Engine_Instr
    import opened BN_Axioms
    import opened RS_Axioms
    import opened Block_Inv_With_Empty_Initial_Block_Slashing_DB
    import opened DV_Block_Proposer_Spec    
    import opened Fnc_Invs_1
    import opened Fnc_Invs_2
    import opened Common_Proofs_For_Block_Proposer
    import opened Invs_DV_Next_1
    import opened Invs_DV_Next_2
    import opened Invs_DV_Next_3
    import opened Invs_DV_Next_4

    lemma lem_inv_block_slashing_db_is_monotonic_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    ) 
    requires NextEvent.requires(dv, event, dv')    
    requires NextEvent(dv, event, dv')  
    ensures inv_block_slashing_db_is_monotonic(dv, event, dv')
    { 
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var process := dv.honest_nodes_states[node];
                var process' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_block_slashing_db_is_monotonic_body_f_serve_proposer_duty(process, proposer_duty, process');
                    
                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_block_slashing_db_is_monotonic_f_listen_for_randao_shares(process, randao_share, process');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(process, id, decided_beacon_block)
                        {
                            lem_inv_block_slashing_db_is_monotonic_body_f_block_consensus_decided(process, id, decided_beacon_block, process');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_block_slashing_db_is_monotonic_f_listen_for_block_signature_shares(process, block_share, process');                        
   
                    case ImportedNewBlock(block) => 
                        var process := f_add_block_to_bn(process, nodeEvent.block);
                        lem_inv_block_slashing_db_is_monotonic_body_f_listen_for_new_imported_blocks(process, block, process');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }
    }

    lemma lem_inv_available_current_proposer_duty_is_from_dv_seq_of_proposer_duties_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEvent.requires(dv, event, dv')  
    requires NextEvent(dv, event, dv')  
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty(dv)
    requires inv_available_current_proposer_duty_is_from_dv_seq_of_proposer_duties(dv)
    ensures inv_available_current_proposer_duty_is_from_dv_seq_of_proposer_duties(dv')
    {        
        lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_dv_next(dv, event, dv');
        lem_inv_available_current_proposer_duty_is_latest_proposer_duty_dv_next(dv, event, dv');
    }   

    lemma lem_NonServeProposerDuty_unchanged_vars(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')      
    requires event.HonestNodeTakingStep?
    requires !event.event.ServeProposerDuty?
    ensures s.index_next_proposer_duty_to_be_served == s'.index_next_proposer_duty_to_be_served;
    ensures s.sequence_proposer_duties_to_be_served == s'.sequence_proposer_duties_to_be_served  
    { }  

    lemma lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_helper_honest(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?    
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(s)
    requires inv_available_current_proposer_duty_is_from_dv_seq_of_proposer_duties(s)
    requires inv_available_current_proposer_duty_is_from_dv_seq_of_proposer_duties(s)
    requires inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist(s)
    ensures inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(s'.sequence_proposer_duties_to_be_served, event.node, s'.honest_nodes_states[event.node], s'.index_next_proposer_duty_to_be_served); 
    {
        assert s.sequence_proposer_duties_to_be_served == s'.sequence_proposer_duties_to_be_served;
        var sequence_proposer_duties_to_be_served := s'.sequence_proposer_duties_to_be_served;

        assert s.block_share_network.allMessagesSent <= s'.block_share_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                
                lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_helper(s, event, s', s_node, node);
                assert inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_proposer_duties_to_be_served, node, s_node, s.index_next_proposer_duty_to_be_served);
                assert inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(s_node);     

                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) => 
                        assert s.index_next_proposer_duty_to_be_served == s'.index_next_proposer_duty_to_be_served - 1;
                        lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_serve_proposer_duty(
                            s_node,
                            proposer_duty,
                            s'_node,
                            sequence_proposer_duties_to_be_served, 
                            node,
                            s'.index_next_proposer_duty_to_be_served
                        );
                        assert inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_proposer_duties_to_be_served, node, s'_node, s'.index_next_proposer_duty_to_be_served);                     
                
                    case ReceiveRandaoShare(randao_share) =>                             
                        lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_listen_for_randao_shares(
                            s_node, 
                            randao_share, 
                            s'_node,
                            sequence_proposer_duties_to_be_served, 
                            node,
                            s'.index_next_proposer_duty_to_be_served
                        );    
                    
                    case BlockConsensusDecided(id, decided_beacon_block) =>  
                        assert s.index_next_proposer_duty_to_be_served == s'.index_next_proposer_duty_to_be_served;    
                        if f_block_consensus_decided.requires(s_node, id, decided_beacon_block)
                        {
                            lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_block_consensus_decided(
                                s_node,
                                id,
                                decided_beacon_block,
                                s'_node,
                                sequence_proposer_duties_to_be_served, 
                                node,
                                s'.index_next_proposer_duty_to_be_served
                            ); 
                        }
                        assert inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_proposer_duties_to_be_served, node, s'_node, s'.index_next_proposer_duty_to_be_served);                        
               
                    case ReceiveSignedBeaconBlock(block_share) =>
                        lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_listen_for_block_signature_shares(
                            s_node, 
                            block_share, 
                            s'_node,
                            sequence_proposer_duties_to_be_served, 
                            node,
                            s'.index_next_proposer_duty_to_be_served
                        );                        
                        assert inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_proposer_duties_to_be_served, node, s'_node, s'.index_next_proposer_duty_to_be_served);  
                        
                    case ImportedNewBlock(block) => 
                        var s_node2 := f_add_block_to_bn(s_node, nodeEvent.block);
                        lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            sequence_proposer_duties_to_be_served, 
                            node,
                            s'.index_next_proposer_duty_to_be_served
                        );  
                        assert inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_proposer_duties_to_be_served, node, s'_node, s'.index_next_proposer_duty_to_be_served);                     
                 
                    case ResendRandaoRevealSignatureShare =>
                        lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_resend_randao_share(
                            s_node,
                            s'_node,
                            sequence_proposer_duties_to_be_served, 
                            node,
                            s'.index_next_proposer_duty_to_be_served
                        ); 
                        assert inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_proposer_duties_to_be_served, node, s'_node, s'.index_next_proposer_duty_to_be_served);                     


                    case ResendBlockShare =>
                        lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_resend_block_share(
                            s_node,
                            s'_node,
                            sequence_proposer_duties_to_be_served, 
                            node,
                            s'.index_next_proposer_duty_to_be_served
                        ); 
                        assert inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_proposer_duties_to_be_served, node, s'_node, s'.index_next_proposer_duty_to_be_served);  

                    case NoEvent => 
                        lem_NonServeProposerDuty_unchanged_vars(s, event, s');
                        assert s_node == s'_node; 
                        assert inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_proposer_duties_to_be_served, node, s'_node, s'.index_next_proposer_duty_to_be_served);                          
                }                     

        }
    }   

    lemma lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_dv_next(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(s)
    requires inv_available_current_proposer_duty_is_from_dv_seq_of_proposer_duties(s)
    requires inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist(s)
    ensures inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist(s')
    {
            match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_helper_honest(
                    s,
                    event,
                    s'
                );

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    }

    lemma lem_inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_dv_next_AdversaryTakingStep(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.AdversaryTakingStep?
    requires inv_all_honest_nodes_is_a_quorum(dv)
    requires inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks(dv)
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db(dv)
    ensures  inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks(dv')
    {        
        match event 
        {
            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                lem_inv_all_honest_nodes_is_a_quorum_dv_next(dv, event, dv');
                assert inv_all_honest_nodes_is_a_quorum(dv');
                var dishonest_nodes := dv'.adversary.nodes;
                var honest_nodes := dv'.honest_nodes_states.Keys;
                lemmaEmptyIntersectionImpliesDisjointness(dishonest_nodes, honest_nodes);
                assert dishonest_nodes !! honest_nodes;

                var new_block_shares := dv'.block_share_network.allMessagesSent - dv.block_share_network.allMessagesSent;
                forall new_block_share: SignedBeaconBlock, signer: BLSPubkey | 
                            (   && new_block_share in new_block_shares
                                && var block_signing_root := compute_block_signing_root(new_block_share.block);
                                && verify_bls_signature(block_signing_root, new_block_share.signature, signer)
                            )
                ensures !is_an_honest_node(dv, signer)
                {
                    assert signer in dishonest_nodes;
                    assert !is_an_honest_node(dv, signer);
                }
                assert inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks(dv');
        }  
    } 

    lemma lem_inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_dv_next_HonestNodeTakingStep(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState,
        node: BLSPubkey, 
        nodeEvent: Types.BlockEvent, 
        nodeOutputs: Outputs
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.HonestNodeTakingStep?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires && var dvc' := dv'.honest_nodes_states[node];
             && inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(nodeOutputs, dvc');
    requires inv_all_honest_nodes_is_a_quorum(dv)
    requires inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks(dv)
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db(dv)
    ensures  inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks(dv')
    {        
        var dvc := dv.honest_nodes_states[node];
        var dvc' := dv'.honest_nodes_states[node];
        assert inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(nodeOutputs, dvc');

        assert  dv.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient(nodeOutputs.sent_block_shares)
                ==
                dv'.block_share_network.allMessagesSent
                ;
        forall hn: BLSPubkey, block_share: SignedBeaconBlock | 
                    && is_an_honest_node(dv, hn)
                    && block_share in dv'.block_share_network.allMessagesSent 
                    && var hn_node': DVCState := dv'.honest_nodes_states[hn];
                    && var hn_rs_pubkey: BLSPubkey := hn_node'.rs.pubkey;
                    && pred_is_the_owner_of_a_block_share(hn_rs_pubkey, block_share)
        ensures && var hn_node': DVCState := dv'.honest_nodes_states[hn];
                && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(hn_node', block_share)            
        {
            var hn_node: DVCState := dv.honest_nodes_states[hn];
            var hn_node': DVCState := dv'.honest_nodes_states[hn];
            var hn_rs_pubkey: BLSPubkey := hn_node'.rs.pubkey;

            lem_inv_unchanged_rs_dv_next(dv, event, dv');         
            assert hn_node.rs.pubkey == hn_node'.rs.pubkey;   

            lem_inv_block_slashing_db_is_monotonic_dv_next(dv, event, dv');     
            assert hn_node.block_slashing_db <= hn_node'.block_slashing_db;      
            

            if block_share in dv.block_share_network.allMessagesSent 
            {
                assert inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(hn_node, block_share);
                
                var beacon_block := block_share.block;
                var slashing_db_block := construct_SlashingDBBlock_from_beacon_block(beacon_block);
                assert slashing_db_block in hn_node.block_slashing_db;
                
                lem_member_of_subset_is_member_of_superset(slashing_db_block, hn_node.block_slashing_db, hn_node'.block_slashing_db);
                assert slashing_db_block in hn_node'.block_slashing_db;

                assert inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(hn_node', block_share);
            }
            else
            {                        
                assert block_share in getMessagesFromMessagesWithRecipient(nodeOutputs.sent_block_shares);
                rs_block_sign_and_verification_propeties();
                assert inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_body(
                            dvc', 
                            block_share
                        );
                assert inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(dvc', block_share);
                assert pred_is_the_owner_of_a_block_share(dvc'.rs.pubkey, block_share);
                assert pred_is_the_owner_of_a_block_share(hn_rs_pubkey, block_share);
                lem_unique_owner_of_block_share(hn_rs_pubkey, dvc'.rs.pubkey, block_share);
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
                assert inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(hn_node', block_share);
            }
        }
    }

    lemma lem_inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_all_honest_nodes_is_a_quorum(dv)
    requires inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks(dv)
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db(dv)
    ensures  inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_serve_proposer_duty(dvc, proposer_duty, dvc');
                        assert inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(nodeOutputs, dvc');  

                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_listen_for_randao_shares(dvc, randao_share, dvc');    
                        assert inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(nodeOutputs, dvc');  
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');      
                            assert inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(nodeOutputs, dvc');  
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_listen_for_block_signature_shares(dvc, block_share, dvc');                        
                        assert inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(nodeOutputs, dvc');  
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_listen_for_new_imported_blocks(dvc, block, dvc');
                        assert inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(nodeOutputs, dvc');  

                    case ResendRandaoRevealSignatureShare =>
                        lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_resend_randao_share(dvc, dvc');
                        assert inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(nodeOutputs, dvc');      
                                                
                    case ReceiveSignedBeaconBlock =>       
                        lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_resend_block_share(dvc, dvc');
                        assert inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(nodeOutputs, dvc');                    
                        
                    case NoEvent => 
                        assert inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(nodeOutputs, dvc');  
                }
                
                assert inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(nodeOutputs, dvc');

                lem_inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_dv_next_HonestNodeTakingStep(
                    dv,
                    event,
                    dv',
                    node, 
                    nodeEvent, 
                    nodeOutputs
                );

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                lem_inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_dv_next_AdversaryTakingStep(
                    dv,
                    event,
                    dv'
                );
        }  
    }  
         
    lemma lem_inv_unchanged_rs_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    ensures ( forall hn: BLSPubkey | is_an_honest_node(dv, hn) ::
                    dv.honest_nodes_states[hn].rs.pubkey
                    ==
                    dv'.honest_nodes_states[hn].rs.pubkey
            )
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var process := dv.honest_nodes_states[node];
                var process' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_unchanged_rs_f_serve_proposer_duty(process, proposer_duty, process');
                    
                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_unchanged_rs_f_listen_for_randao_shares(process, randao_share, process');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(process, id, decided_beacon_block)
                        {
                            lem_inv_unchanged_rs_f_block_consensus_decided(process, id, decided_beacon_block, process');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_unchanged_rs_f_listen_for_block_signature_shares(process, block_share, process');                        
   
                    case ImportedNewBlock(block) => 
                        var process := f_add_block_to_bn(process, nodeEvent.block);
                        lem_inv_unchanged_rs_f_listen_for_new_imported_blocks(process, block, process');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        } 
    }
    
    lemma lem_inv_all_created_signed_beacon_blocks_are_valid_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_only_dv_construct_complete_signing_functions(dv)
    requires inv_all_created_signed_beacon_blocks_are_valid(dv)
    ensures  inv_all_created_signed_beacon_blocks_are_valid(dv')
    {        
        lem_inv_only_dv_construct_complete_signing_functions_dv_next(dv, event, dv');
        assert inv_only_dv_construct_complete_signing_functions(dv');

        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_submitted_outputs_blocks_are_valid_f_serve_proposer_duty(dvc, proposer_duty, dvc');

                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_submitted_outputs_blocks_are_valid_f_listen_for_randao_shares(dvc, randao_share, dvc');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            lem_inv_submitted_outputs_blocks_are_valid_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_submitted_outputs_blocks_are_valid_f_listen_for_block_signature_shares(dvc, block_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_submitted_outputs_blocks_are_valid_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ReceiveSignedBeaconBlock =>                         
                        
                    case NoEvent => 
                        
                }

                assert inv_submitted_outputs_blocks_are_valid(nodeOutputs, dv.dv_pubkey);
                assert inv_all_created_signed_beacon_blocks_are_valid(dv');

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                assert  NextAdversary(dv, node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode, dv');                        
                
                var new_aggregated_blocks_sent := dv'.all_blocks_created - dv.all_blocks_created;

                forall aggregated_block_sent | aggregated_block_sent in new_aggregated_blocks_sent 
                ensures is_verified_block_with_pubkey(aggregated_block_sent, dv.dv_pubkey)
                {
                    assert is_verified_block_with_pubkey(aggregated_block_sent, dv.dv_pubkey);
                }
                                
                assert inv_all_created_signed_beacon_blocks_are_valid(dv');
        }  
    }  
    
    lemma lem_inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_dv_next_AdversaryTakingStep(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.AdversaryTakingStep?
    requires inv_only_dv_construct_complete_signing_functions(dv)
    requires inv_in_transit_messages_are_in_allMessagesSent(dv)
    requires inv_rcvd_block_shares_are_in_all_sent_messages(dv)
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum(dv)
    ensures  inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum(dv')
    {        
        lem_inv_only_dv_construct_complete_signing_functions_dv_next(dv, event, dv');
        assert inv_only_dv_construct_complete_signing_functions(dv');

        lem_inv_unchanged_dvc_rs_pubkey_dv_next(dv, event, dv');
        assert ( forall hn: BLSPubkey | is_an_honest_node(dv, hn) ::
                        && hn == dv.honest_nodes_states[hn].rs.pubkey
                        && hn == dv'.honest_nodes_states[hn].rs.pubkey
        );

        lem_inv_rcvd_block_shares_are_in_all_sent_messages_dv_next(dv, event, dv');

        match event 
        {
            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                assert NextAdversary(
                    dv,
                    node,
                    new_randao_shares_sent,
                    new_sent_block_shares,
                    randaoShareReceivedByTheNode,
                    blockShareReceivedByTheNode,
                    dv'
                );
                
                var new_blocks_created := dv'.all_blocks_created - dv.all_blocks_created;

                forall new_signed_block_created | new_signed_block_created in new_blocks_created 
                ensures inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_body(dv', new_signed_block_created)
                {
                    assert inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_body(dv', new_signed_block_created);
                }
                                
                assert inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum(dv');
        }  
    } 

    lemma lem_inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_dv_next_HonestNodeTakingStep(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState,
        node: BLSPubkey, 
        nodeEvent: Types.BlockEvent, 
        nodeOutputs: Outputs
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.HonestNodeTakingStep?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires && var dvc' := dv'.honest_nodes_states[node];
             && inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum(
                    nodeOutputs,
                    dvc'
                )
    requires inv_only_dv_construct_complete_signing_functions(dv)
    requires ( forall hn: BLSPubkey | is_an_honest_node(dv, hn) ::
                        && hn == dv.honest_nodes_states[hn].rs.pubkey
                        && hn == dv'.honest_nodes_states[hn].rs.pubkey
            );
    requires inv_rcvd_block_shares_are_in_all_sent_messages(dv')    
    requires inv_in_transit_messages_are_in_allMessagesSent(dv)
    requires inv_rcvd_block_shares_are_in_all_sent_messages(dv)
    requires inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum(dv)   
    requires inv_unchanged_dvc_rs_pubkey(dv)
    ensures inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum(dv')
    {        
        var dvc := dv.honest_nodes_states[node];
        var dvc' := dv'.honest_nodes_states[node];

        assert inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum(nodeOutputs, dvc');
        assert dv'.all_blocks_created == dv.all_blocks_created + nodeOutputs.submitted_data;

        forall complete_signed_block: SignedBeaconBlock | complete_signed_block in dv'.all_blocks_created 
        ensures inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_body(dv', complete_signed_block)
        {
            if complete_signed_block in dv.all_blocks_created 
            {
                assert inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_body(dv, complete_signed_block);
                var block_shares, dvc_signer_pubkeys :|
                        && block_shares <= dv.block_share_network.allMessagesSent
                        && dv.construct_complete_signed_block(block_shares).isPresent()
                        && complete_signed_block == dv.construct_complete_signed_block(block_shares).safe_get()
                        && signed_beacon_blocks_for_the_same_beacon_block(block_shares, complete_signed_block.block)
                        && dvc_signer_pubkeys <= dv.all_nodes
                        && inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_body_signers(dv, block_shares, dvc_signer_pubkeys)
                        && |dvc_signer_pubkeys| >= quorum(|dv.all_nodes|)
                        && dvc_signer_pubkeys <= dv.all_nodes
                        ;
                
                assert dv.block_share_network.allMessagesSent <= dv'.block_share_network.allMessagesSent;
                assert block_shares <= dv'.block_share_network.allMessagesSent;

                lem_inv_only_dv_construct_complete_signing_functions_dv_next(dv, event, dv');                        
                assert  dv.construct_complete_signed_block == dv'.construct_complete_signed_block;
                assert  complete_signed_block == dv'.construct_complete_signed_block(block_shares).safe_get();

                assert  dvc_signer_pubkeys <= dv'.all_nodes;

                assert  inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_body_signers(dv', block_shares, dvc_signer_pubkeys);
                assert  inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_body(dv', complete_signed_block);
            }
            else
            {
                assert complete_signed_block in nodeOutputs.submitted_data;
                assert inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum_body(dvc', complete_signed_block);

                var block_shares, rs_signer_pubkeys, k :|        
                            && k in dvc'.rcvd_block_shares[complete_signed_block.block.slot].Keys
                            && block_shares <= dvc'.rcvd_block_shares[complete_signed_block.block.slot][k]
                            && dvc'.construct_complete_signed_block(block_shares).isPresent()
                            && complete_signed_block == dvc'.construct_complete_signed_block(block_shares).safe_get()
                            && signed_beacon_blocks_for_the_same_beacon_block(block_shares, complete_signed_block.block)
                            && inv_a_complete_block_is_created_based_on_shares_from_a_quorum_of_rs_signers(block_shares, rs_signer_pubkeys)
                            && |rs_signer_pubkeys| >= quorum(|dvc'.peers|)
                            && rs_signer_pubkeys <= dvc'.peers
                            ;

                assert  dvc'.peers == dv'.all_nodes;
                assert  quorum(|dvc'.peers|) == quorum(|dv'.all_nodes|);
                assert  |rs_signer_pubkeys| >= quorum(|dvc'.peers|);
                assert  && |rs_signer_pubkeys| >= quorum(|dv'.all_nodes|)
                        && rs_signer_pubkeys <= dv'.all_nodes;

                lem_inv_only_dv_construct_complete_signing_functions_dv_next(dv, event, dv');                        
                assert  dv.construct_complete_signed_block == dv'.construct_complete_signed_block;
                assert  dv'.construct_complete_signed_block(block_shares).isPresent();
                assert  complete_signed_block == dv'.construct_complete_signed_block(block_shares).safe_get();

                lem_inv_rcvd_block_shares_are_in_all_sent_messages_dv_next(dv, event, dv');  
                assert dvc'.rcvd_block_shares[complete_signed_block.block.slot][k] <= dv'.block_share_network.allMessagesSent;   
                assert block_shares <= dv'.block_share_network.allMessagesSent;   
                assert  block_shares <= dv'.block_share_network.allMessagesSent;   

                assert  inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_body_signers(dv', block_shares, rs_signer_pubkeys);                
                assert inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_body(dv', complete_signed_block);
            }
        }
        assert inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum(dv');            
    }  

    lemma lem_inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_only_dv_construct_complete_signing_functions(dv)
    requires inv_in_transit_messages_are_in_allMessagesSent(dv)
    requires inv_rcvd_block_shares_are_in_all_sent_messages(dv)
    requires inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum(dv)
    requires inv_unchanged_dvc_rs_pubkey(dv)
    ensures  inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum(dv')
    {        
        lem_inv_only_dv_construct_complete_signing_functions_dv_next(dv, event, dv');
        assert inv_only_dv_construct_complete_signing_functions(dv');

        lem_inv_unchanged_dvc_rs_pubkey_dv_next(dv, event, dv');
        assert ( forall hn: BLSPubkey | is_an_honest_node(dv, hn) ::
                        && hn == dv.honest_nodes_states[hn].rs.pubkey
                        && hn == dv'.honest_nodes_states[hn].rs.pubkey
        );

        lem_inv_rcvd_block_shares_are_in_all_sent_messages_dv_next(dv, event, dv');

        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum_f_serve_proposer_duty(dvc, proposer_duty, dvc');
                    
                    case ReceiveRandaoShare(randao_share) =>
                        lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum_f_listen_for_randao_shares(dvc, randao_share, dvc');
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum_f_listen_for_block_signature_shares(dvc, block_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ReceiveSignedBeaconBlock =>   
                        lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum_f_resend_block_share(dvc, dvc');

                    case ResendRandaoRevealSignatureShare =>                      
                        lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum_f_resend_randao_share(dvc, dvc');
                        
                    case NoEvent => 
                }

                assert inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum(nodeOutputs, dvc');

                lem_inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_dv_next_HonestNodeTakingStep(
                    dv,
                    event,
                    dv',
                    node, 
                    nodeEvent, 
                    nodeOutputs
                );

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                lem_inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_dv_next_AdversaryTakingStep(
                    dv,
                    event,
                    dv'
                );
        }  
    }   
    
    lemma lem_inv_slots_for_sent_validity_predicates_are_stored_in_slashing_db_hist_implies_46_a(dv: DVState)
    requires inv_slots_for_sent_validity_predicates_are_stored_in_slashing_db_hist(dv)
    ensures inv_sent_validity_predicate_only_for_slots_stored_in_slashing_db_hist(dv)
    {
        forall hn: BLSPubkey, s: Slot | is_an_honest_node(dv, hn)
        ensures
                var hn_state := dv.honest_nodes_states[hn];
                && ( hn in dv.consensus_instances_on_beacon_block[s].honest_nodes_validity_functions.Keys
                    ==> s in hn_state.block_consensus_engine_state.slashing_db_hist.Keys)
                ;        
        {
            assert hn in dv.honest_nodes_states.Keys;
            var hn_state := dv.honest_nodes_states[hn];
            assert inv_slots_for_sent_validity_predicates_are_stored_in_slashing_db_hist_body(dv, hn, hn_state, s);
            assert
                && ( hn in dv.consensus_instances_on_beacon_block[s].honest_nodes_validity_functions.Keys
                    ==> s in hn_state.block_consensus_engine_state.slashing_db_hist.Keys)
                ;
        }
    }  

    lemma lem_inv_sent_validity_predicate_only_for_slots_stored_in_slashing_db_hist(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires inv_only_dv_construct_complete_signing_functions(s)   
    requires inv_slots_for_sent_validity_predicates_are_stored_in_slashing_db_hist(s)   
    requires inv_sent_validity_predicate_only_for_slots_stored_in_slashing_db_hist(s)   
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(s)
    ensures inv_sent_validity_predicate_only_for_slots_stored_in_slashing_db_hist(s')   
    {
        lem_inv_slots_for_sent_validity_predicates_are_stored_in_slashing_db_hist(s, event, s');
        lem_inv_slots_for_sent_validity_predicates_are_stored_in_slashing_db_hist_implies_46_a(s');
    }     

    lemma lem_add_set_of_validity_predicates2<D(!new, 0)>(
        existing_honest_nodes_validity_predicates: map<BLSPubkey, set<D -> bool>>,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,
        new_honest_nodes_validity_predicates: map<BLSPubkey, set<D -> bool>>,
        n: BLSPubkey,
        vp: D -> bool
    )
    requires new_honest_nodes_validity_predicates == add_set_of_validity_predicates(existing_honest_nodes_validity_predicates, honest_nodes_validity_predicates)
    requires n in existing_honest_nodes_validity_predicates.Keys
    requires vp !in existing_honest_nodes_validity_predicates[n]
    requires vp in new_honest_nodes_validity_predicates[n]
    ensures vp == honest_nodes_validity_predicates[n]
    ensures new_honest_nodes_validity_predicates.Keys == existing_honest_nodes_validity_predicates.Keys + new_honest_nodes_validity_predicates.Keys
    { }    

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
    { }      

    function f_inv_all_validity_predicates_are_stored_in_slashing_db_hist_body_helper_helper_function(
        s_w_honest_node_states_updated: DVState,
        cid: Slot
    ) : map<BLSPubkey, BeaconBlock -> bool>
    {
        map n |
                && n in s_w_honest_node_states_updated.honest_nodes_states.Keys 
                && cid in s_w_honest_node_states_updated.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances.Keys
            ::
                s_w_honest_node_states_updated.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances[cid].validityPredicate
    }    

    lemma lem_slashing_db_hist_cid_is_monotonic(
        s: DVCState,
        event: Types.BlockEvent,
        s': DVCState,
        outputs: Outputs,
        cid: Slot       
    )
    requires DVC_Block_Proposer_Spec_Instr.Next.requires(s, event, s', outputs)
    requires DVC_Block_Proposer_Spec_Instr.Next(s, event, s', outputs)
    requires cid in s.block_consensus_engine_state.slashing_db_hist.Keys
    ensures cid in s'.block_consensus_engine_state.slashing_db_hist.Keys
    ensures s.block_consensus_engine_state.slashing_db_hist[cid].Keys <= s'.block_consensus_engine_state.slashing_db_hist[cid].Keys;  
    { } 

    lemma lem_slashing_db_hist_cid_is_monotonic_corollary(
        s: DVCState,
        event: Types.BlockEvent,
        s': DVCState,
        outputs: Outputs,
        cid: Slot,
        vp: BeaconBlock -> bool       
    )
    requires DVC_Block_Proposer_Spec_Instr.Next.requires(s, event, s', outputs)    
    requires DVC_Block_Proposer_Spec_Instr.Next(s, event, s', outputs)
    requires cid in s.block_consensus_engine_state.slashing_db_hist.Keys
    requires vp in s.block_consensus_engine_state.slashing_db_hist[cid].Keys
    ensures cid in s'.block_consensus_engine_state.slashing_db_hist.Keys
    ensures vp in s'.block_consensus_engine_state.slashing_db_hist[cid].Keys
    {
        lem_slashing_db_hist_cid_is_monotonic(s, event, s', outputs, cid);
    }     


    lemma lem_inv_all_validity_predicates_are_stored_in_slashing_db_hist_helper_AdversaryTakingStep(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,        
        s': DVState,
        hn: BLSPubkey
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.AdversaryTakingStep?
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires inv_only_dv_construct_complete_signing_functions(s)    
    requires hn in s.honest_nodes_states.Keys
    requires inv_slots_for_sent_validity_predicates_are_stored_in_slashing_db_hist(s)
    
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(s)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(s.honest_nodes_states[hn])
    requires inv_all_validity_predicates_are_stored_in_slashing_db_hist_helper(s, hn)
    ensures inv_all_validity_predicates_are_stored_in_slashing_db_hist_helper(s', hn)
    {
        assert s.block_share_network.allMessagesSent <= s'.block_share_network.allMessagesSent;
        assert s'.consensus_instances_on_beacon_block == s.consensus_instances_on_beacon_block;
        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];

        var hn_state' := s'.honest_nodes_states[hn];

        forall cid: Slot, vp: BeaconBlock -> bool |
                    && hn in s'.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions.Keys
                    && vp in s'.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions[hn]                          
                    && cid in s'.honest_nodes_states[hn].block_consensus_engine_state.slashing_db_hist.Keys
        ensures inv_all_validity_predicates_are_stored_in_slashing_db_hist_body(
                    s',
                    hn,
                    hn_state',
                    cid,
                    vp
                )
        {
            assert inv_slots_for_sent_validity_predicates_are_stored_in_slashing_db_hist_body(s, hn, s.honest_nodes_states[hn], cid);
            assert inv_all_validity_predicates_are_stored_in_slashing_db_hist_body(s, hn, s.honest_nodes_states[hn], cid, vp);
            assert inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(s.honest_nodes_states[hn]);
            assert inv_slots_for_sent_validity_predicates_are_stored_in_slashing_db_hist_body(s, hn, s.honest_nodes_states[hn], cid);
            assert cid in s.honest_nodes_states[hn].block_consensus_engine_state.slashing_db_hist.Keys;
            assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
            assert cid in s'.honest_nodes_states[hn].block_consensus_engine_state.slashing_db_hist.Keys;
            assert vp in s'.honest_nodes_states[hn].block_consensus_engine_state.slashing_db_hist[cid].Keys;
        }   
        
    }  

    predicate pred_all_validity_predicates_are_stored_in_slashing_db_hist_helper_HonestNodeTakingStep_lopp_support(
                    s: DVState,
                    hn: BLSPubkey,
                    cid: Slot, 
                    vp : BeaconBlock -> bool
                )             
    {
        && hn in s.honest_nodes_states.Keys
        && var hn_state := s.honest_nodes_states[hn];
        && cid in hn_state.block_consensus_engine_state.slashing_db_hist.Keys        
        && vp in hn_state.block_consensus_engine_state.slashing_db_hist[cid].Keys
    }

    lemma lem_inv_all_validity_predicates_are_stored_in_slashing_db_hist_helper_HonestNodeTakingStep_loop_helper(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,        
        s': DVState,
        hn: BLSPubkey,
        node: BLSPubkey, 
        nodeEvent: Types.BlockEvent, 
        nodeOutputs: Outputs,
        cid: Slot, 
        vp : BeaconBlock -> bool
    )    
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)    
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires inv_only_dv_construct_complete_signing_functions(s)    
    requires hn in s.honest_nodes_states.Keys
    requires inv_slots_for_sent_validity_predicates_are_stored_in_slashing_db_hist(s)
    requires inv_all_validity_predicates_are_stored_in_slashing_db_hist_helper(s, hn)
    requires inv_constraints_on_active_consensus_instances_are_ensured_with_slashing_db_hist(s)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(s)
    requires && var hn_state' := s'.honest_nodes_states[hn];
             && hn in s'.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions.Keys
             && cid in hn_state'.block_consensus_engine_state.slashing_db_hist.Keys
             && vp in s'.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions[hn]
    ensures pred_all_validity_predicates_are_stored_in_slashing_db_hist_helper_HonestNodeTakingStep_lopp_support(
                    s,
                    hn,
                    cid, 
                    vp
                )
    {
        assert s.block_share_network.allMessagesSent <= s'.block_share_network.allMessagesSent;

        var s_w_honest_node_states_updated := f_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_get_s_w_honest_node_states_updated(s, node, nodeEvent);           

        assert s_w_honest_node_states_updated.consensus_instances_on_beacon_block == s.consensus_instances_on_beacon_block;

        var hn_state := s.honest_nodes_states[hn];
        var hn_state' := s'.honest_nodes_states[hn];

        var output := 
                if nodeEvent.BlockConsensusDecided? && nodeEvent.id == cid then 
                    Some(Decided(node, nodeEvent.decided_beacon_block))
                else
                    None
                ;

        var validityPredicates := f_inv_all_validity_predicates_are_stored_in_slashing_db_hist_body_helper_helper_function(s_w_honest_node_states_updated, cid);                    

        assert  && cid in s_w_honest_node_states_updated.consensus_instances_on_beacon_block.Keys
                && cid in s'.consensus_instances_on_beacon_block.Keys
                ;
        var s_consensus := s_w_honest_node_states_updated.consensus_instances_on_beacon_block[cid];
        var s'_consensus := s'.consensus_instances_on_beacon_block[cid];                

        assert  ConsensusSpec.Next(
                    s_consensus,
                    validityPredicates,
                    s'_consensus,
                    output
                );
        
        
        if hn in s.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions.Keys
        {
            if vp in s.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions[hn]
            {
                assert  inv_constraints_on_active_consensus_instances_are_ensured_with_slashing_db_hist_body(
                            hn_state,
                            cid
                        );

                assert  && hn in s.honest_nodes_states.Keys
                        && hn_state == s.honest_nodes_states[hn]
                        && hn in s.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions.Keys
                        && vp in s.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions[hn]
                        ;

                assert  s_w_honest_node_states_updated.consensus_instances_on_beacon_block.Keys
                        ==
                        s.consensus_instances_on_beacon_block.Keys
                        ;
                assert  cid in s.consensus_instances_on_beacon_block.Keys;
                assert  hn in s.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions.Keys;
                assert  inv_slots_for_sent_validity_predicates_are_stored_in_slashing_db_hist_body(
                            s,
                            hn,
                            hn_state,
                            cid
                        );
                assert  cid in hn_state.block_consensus_engine_state.slashing_db_hist.Keys;
                assert  vp in s.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions[hn];
                assert  inv_all_validity_predicates_are_stored_in_slashing_db_hist_body(
                            s, 
                            hn,
                            hn_state,
                            cid,
                            vp
                        );
                assert vp in hn_state.block_consensus_engine_state.slashing_db_hist[cid].Keys;
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

                assert  vp == s.honest_nodes_states[hn].block_consensus_engine_state.active_consensus_instances[cid].validityPredicate; 
                assert  cid in hn_state.block_consensus_engine_state.active_consensus_instances.Keys;
                assert  inv_constraints_on_active_consensus_instances_are_ensured_with_slashing_db_hist_body(
                            hn_state,
                            cid
                        );
                assert vp in hn_state.block_consensus_engine_state.slashing_db_hist[cid].Keys;
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

            assert  vp == s.honest_nodes_states[hn].block_consensus_engine_state.active_consensus_instances[cid].validityPredicate; 
            assert  cid in hn_state.block_consensus_engine_state.active_consensus_instances.Keys;
            assert  inv_constraints_on_active_consensus_instances_are_ensured_with_slashing_db_hist_body(
                        hn_state,
                        cid
                    );
            assert vp in hn_state.block_consensus_engine_state.slashing_db_hist[cid].Keys;
        }

        assert  pred_all_validity_predicates_are_stored_in_slashing_db_hist_helper_HonestNodeTakingStep_lopp_support(
                    s,
                    hn,
                    cid, 
                    vp
                );
    }

    lemma lem_inv_all_validity_predicates_are_stored_in_slashing_db_hist_helper_HonestNodeTakingStep(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,        
        s': DVState,
        hn: BLSPubkey,
        node: BLSPubkey, 
        nodeEvent: Types.BlockEvent, 
        nodeOutputs: Outputs
    )    
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)    
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires inv_only_dv_construct_complete_signing_functions(s)    
    requires hn in s.honest_nodes_states.Keys
    requires inv_slots_for_sent_validity_predicates_are_stored_in_slashing_db_hist(s)
    requires inv_all_validity_predicates_are_stored_in_slashing_db_hist_helper(s, hn)
    requires inv_constraints_on_active_consensus_instances_are_ensured_with_slashing_db_hist(s)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(s)
    ensures inv_all_validity_predicates_are_stored_in_slashing_db_hist_helper(s', hn)
    {
        assert s.block_share_network.allMessagesSent <= s'.block_share_network.allMessagesSent;

        var s_w_honest_node_states_updated := f_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_get_s_w_honest_node_states_updated(s, node, nodeEvent);           

        assert s_w_honest_node_states_updated.consensus_instances_on_beacon_block == s.consensus_instances_on_beacon_block;

        var hn_state := s.honest_nodes_states[hn];
        var hn_state' := s'.honest_nodes_states[hn];

        forall cid: Slot, vp : BeaconBlock -> bool |
                    && hn in s'.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions.Keys
                    && cid in hn_state'.block_consensus_engine_state.slashing_db_hist.Keys
                    && vp in s'.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions[hn]
        ensures inv_all_validity_predicates_are_stored_in_slashing_db_hist_body(
                    s', 
                    hn,
                    hn_state',
                    cid,
                    vp
                )
        {
            var output := 
                if nodeEvent.BlockConsensusDecided? && nodeEvent.id == cid then 
                    Some(Decided(node, nodeEvent.decided_beacon_block))
                else
                    None
                ;

            var validityPredicates := f_inv_all_validity_predicates_are_stored_in_slashing_db_hist_body_helper_helper_function(s_w_honest_node_states_updated, cid);                    

            assert  && cid in s_w_honest_node_states_updated.consensus_instances_on_beacon_block.Keys
                    && cid in s'.consensus_instances_on_beacon_block.Keys
                    ;
            var s_consensus := s_w_honest_node_states_updated.consensus_instances_on_beacon_block[cid];
            var s'_consensus := s'.consensus_instances_on_beacon_block[cid];                

            assert  ConsensusSpec.Next(
                        s_consensus,
                        validityPredicates,
                        s'_consensus,
                        output
                    );
            
            lem_inv_all_validity_predicates_are_stored_in_slashing_db_hist_helper_HonestNodeTakingStep_loop_helper(
                s,
                event,
                s',
                hn,
                node,
                nodeEvent,
                nodeOutputs,
                cid,
                vp
            );

            assert  && cid in hn_state.block_consensus_engine_state.slashing_db_hist.Keys        
                    && vp in hn_state.block_consensus_engine_state.slashing_db_hist[cid].Keys
                    ;

            if hn == node 
            {
                lem_NextEvent_implies_NextHonestAfterAddingBlockToBn_and_DVC_Spec_Next(s, event, s');

                assert DVC_Block_Proposer_Spec_Instr.Next.requires(s_w_honest_node_states_updated.honest_nodes_states[hn], nodeEvent, s'.honest_nodes_states[hn], nodeOutputs);
                assert DVC_Block_Proposer_Spec_Instr.Next(s_w_honest_node_states_updated.honest_nodes_states[hn], nodeEvent, s'.honest_nodes_states[hn], nodeOutputs);
                
                lem_slashing_db_hist_cid_is_monotonic_corollary(s_w_honest_node_states_updated.honest_nodes_states[hn], nodeEvent, s'.honest_nodes_states[hn], nodeOutputs, cid, vp);
                assert vp in hn_state'.block_consensus_engine_state.slashing_db_hist[cid].Keys;
            }
            else 
            {
                assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                assert vp in hn_state'.block_consensus_engine_state.slashing_db_hist[cid].Keys;
            }   
            assert vp in hn_state'.block_consensus_engine_state.slashing_db_hist[cid].Keys; 
        }
    }

    lemma lem_inv_all_validity_predicates_are_stored_in_slashing_db_hist_helper_dv_next(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState,
        hn: BLSPubkey
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires inv_only_dv_construct_complete_signing_functions(s)    
    requires hn in s.honest_nodes_states.Keys
    requires inv_slots_for_sent_validity_predicates_are_stored_in_slashing_db_hist(s)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(s)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(s.honest_nodes_states[hn])
    requires inv_constraints_on_active_consensus_instances_are_ensured_with_slashing_db_hist(s)
    requires inv_all_validity_predicates_are_stored_in_slashing_db_hist_helper(s, hn)
    ensures inv_all_validity_predicates_are_stored_in_slashing_db_hist_helper(s', hn)
    {
        assert s.block_share_network.allMessagesSent <= s'.block_share_network.allMessagesSent;
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                lem_inv_all_validity_predicates_are_stored_in_slashing_db_hist_helper_HonestNodeTakingStep(
                    s,
                    event,                    
                    s',
                    hn,
                    node, 
                    nodeEvent, 
                    nodeOutputs
                );
                
            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) => 
                lem_inv_all_validity_predicates_are_stored_in_slashing_db_hist_helper_AdversaryTakingStep(
                    s,
                    event,                    
                    s',
                    hn
                );
        }
    } 

    lemma lem_inv_all_validity_predicates_are_stored_in_slashing_db_hist_dv_next(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires inv_only_dv_construct_complete_signing_functions(s)    
    requires inv_slots_for_sent_validity_predicates_are_stored_in_slashing_db_hist(s)  
    requires inv_all_validity_predicates_are_stored_in_slashing_db_hist(s) 
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(s)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(s)
    requires inv_constraints_on_active_consensus_instances_are_ensured_with_slashing_db_hist(s)
    ensures inv_all_validity_predicates_are_stored_in_slashing_db_hist(s')   
    {
        forall hn: BLSPubkey | hn in s'.honest_nodes_states.Keys
        ensures inv_all_validity_predicates_are_stored_in_slashing_db_hist_helper(s', hn)    
        {
            lem_inv_all_validity_predicates_are_stored_in_slashing_db_hist_helper_dv_next(s, event, s', hn);
        }
    }  

    lemma lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_dv_next(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(s)        
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(s)  
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(s)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty(s)
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(s)
    requires inv_seq_of_proposer_duties_is_ordered(s);
    ensures inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(s');  
    {
        assert s.block_share_network.allMessagesSent <= s'.block_share_network.allMessagesSent;
        match event 
        {            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var process := s.honest_nodes_states[node];
                var process' := s'.honest_nodes_states[node];
                
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_serve_proposer_duty(process, proposer_duty, process');
                    
                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_listen_for_randao_shares(process, randao_share, process');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(process, id, decided_beacon_block)
                        {
                            lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_block_consensus_decided(process, id, decided_beacon_block, process');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_listen_for_block_signature_shares(process, block_share, process');                        
   
                    case ImportedNewBlock(block) => 
                        var process := f_add_block_to_bn(process, nodeEvent.block);
                        lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_listen_for_new_imported_blocks(process, block, process');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }
                   
            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>

        }
    }   
    
    lemma lem_inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block_f_add_block_to_bn_with_event(
        dv: DVState,
        node: BLSPubkey, 
        nodeEvent: Types.BlockEvent, 
        dv': DVState
    )    
    requires add_block_to_bn_with_event.requires(dv, node, nodeEvent)
    requires dv' == add_block_to_bn_with_event(dv, node, nodeEvent)
    requires inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block(dv)
    ensures  inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block(dv')
    { }   

    lemma lem_inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block_ConsensusSpec_NextConsensusDecides<D(!new, 0)>(
        s: ConsensusInstance,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,        
        s': ConsensusInstance
    )    
    requires && ConsensusSpec.NextConsensusDecides.requires(s, honest_nodes_validity_predicates, s')
             && ConsensusSpec.NextConsensusDecides(s, honest_nodes_validity_predicates, s')
    requires inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block_body(s)
    requires isConditionForSafetyTrue(s)
    ensures  inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block_body(s')
    { }

    lemma lem_inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block_ConsensusSpec_Next<D(!new, 0)>(
        s: ConsensusInstance,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,        
        s': ConsensusInstance,
        output: Optional<OutCommand>
    )    
    requires && ConsensusSpec.Next.requires(s, honest_nodes_validity_predicates, s', output)
             && ConsensusSpec.Next(s, honest_nodes_validity_predicates, s', output)
    requires inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block_body(s)
    requires isConditionForSafetyTrue(s)
    ensures  inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block_body(s')
    {
        lem_inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block_ConsensusSpec_NextConsensusDecides(s, honest_nodes_validity_predicates, s');
    }

    lemma lem_inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block_ConsensusInstanceStep(
        dv: DVState,
        node: BLSPubkey, 
        nodeEvent: Types.BlockEvent, 
        nodeOutputs: Outputs,
        dv': DVState
    )    
    requires && DV_Block_Proposer_Spec.ConsensusInstanceStep.requires(dv, node, nodeEvent, nodeOutputs, dv')
             && DV_Block_Proposer_Spec.ConsensusInstanceStep(dv, node, nodeEvent, nodeOutputs, dv')
    requires inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block(dv)
    requires inv_consensus_instance_isConditionForSafetyTrue(dv)
    ensures  inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block(dv')
    {        
        forall cid | cid in dv.consensus_instances_on_beacon_block.Keys 
        ensures inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block_body(dv'.consensus_instances_on_beacon_block[cid])
        {
            assert isConditionForSafetyTrue(dv.consensus_instances_on_beacon_block[cid]);

            var output := 
                if nodeEvent.BlockConsensusDecided? && nodeEvent.id == cid then 
                    Some(Decided(node, nodeEvent.decided_beacon_block))
                else
                    None
                ;

            var validityPredicates := 
                map n |
                        && n in dv.honest_nodes_states.Keys 
                        && cid in dv.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances.Keys
                    ::
                        dv.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances[cid].validityPredicate
                ;

            assert  ConsensusSpec.Next(
                        dv.consensus_instances_on_beacon_block[cid],
                        validityPredicates,
                        dv'.consensus_instances_on_beacon_block[cid],
                        output
                        );

            lem_inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block_ConsensusSpec_Next(
                dv.consensus_instances_on_beacon_block[cid],
                validityPredicates,
                dv'.consensus_instances_on_beacon_block[cid],
                output
                );
        }
            
    } 

    lemma lem_inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block_NextHonestAfterAddingBlockToBn(
        dv: DVState,
        node: BLSPubkey, 
        nodeEvent: Types.BlockEvent, 
        nodeOutputs: Outputs,
        dv': DVState
    )    
    requires && DV_Block_Proposer_Spec.NextHonestAfterAddingBlockToBn.requires(dv, node, nodeEvent, nodeOutputs, dv')
             && DV_Block_Proposer_Spec.NextHonestAfterAddingBlockToBn(dv, node, nodeEvent, nodeOutputs, dv')
    requires inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block(dv)
    requires inv_consensus_instance_isConditionForSafetyTrue(dv)
    ensures  inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block(dv')
    {        
        assert ConsensusInstanceStep(dv, node, nodeEvent, nodeOutputs, dv');
        lem_inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block_ConsensusInstanceStep(dv, node, nodeEvent, nodeOutputs, dv');
    } 

    lemma lem_inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block_NextHonestNode(
        dv: DVState,
        node: BLSPubkey, 
        nodeEvent: Types.BlockEvent, 
        nodeOutputs: Outputs,
        dv': DVState
    )    
    requires && DV_Block_Proposer_Spec.NextHonestNode.requires(dv, node, nodeEvent, nodeOutputs, dv')
             && DV_Block_Proposer_Spec.NextHonestNode(dv, node, nodeEvent, nodeOutputs, dv')
    requires inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block(dv)
    requires inv_consensus_instance_isConditionForSafetyTrue(dv)
    ensures  inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block(dv')
    {        
        assert node in dv.honest_nodes_states.Keys;
        var dv_w_honest_node_states_updated := add_block_to_bn_with_event(dv, node, nodeEvent);

        lem_inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block_f_add_block_to_bn_with_event(            
            dv, 
            node, 
            nodeEvent, 
            dv_w_honest_node_states_updated
            );

        assert NextHonestAfterAddingBlockToBn(dv_w_honest_node_states_updated, node, nodeEvent, nodeOutputs, dv');

        lem_inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block_NextHonestAfterAddingBlockToBn(
            dv_w_honest_node_states_updated, 
            node, 
            nodeEvent, 
            nodeOutputs, dv');
    }   

    lemma lem_inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block(dv)
    requires inv_consensus_instance_isConditionForSafetyTrue(dv)
    ensures  inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                lem_inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block_NextHonestNode(
                    dv,
                    node, 
                    nodeEvent, 
                    nodeOutputs,
                    dv'
                );    

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                assert inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block(dv');
        }   
    }          

    lemma lem_different_signers_cannot_generate_the_same_block_share(
        rs_pubkey: BLSPubkey,
        rs_pubkey': BLSPubkey,
        block_share: SignedBeaconBlock
    )
    requires rs_pubkey != rs_pubkey'
    requires pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
    ensures !pred_is_the_owner_of_a_block_share(rs_pubkey', block_share)
    {
        if pred_is_the_owner_of_a_block_share(rs_pubkey', block_share)
        {
            lem_unique_owner_of_block_share(rs_pubkey, rs_pubkey', block_share);
        }        
    }

    lemma lem_inv_honest_nodes_are_not_owners_of_block_shares_from_adversary(
        dv: DVState
    )
    requires inv_all_honest_nodes_is_a_quorum(dv)
    ensures inv_honest_nodes_are_not_owners_of_block_shares_from_adversary(dv)
    {
        var honest_nodes := dv.honest_nodes_states.Keys;
        var dishonest_nodes := dv.adversary.nodes;
        lemmaEmptyIntersectionImpliesDisjointness(honest_nodes, dishonest_nodes);
        assert honest_nodes !! dishonest_nodes;

        forall byz_node: BLSPubkey, block_share: SignedBeaconBlock | 
            && byz_node in dv.adversary.nodes 
            && block_share in dv.block_share_network.allMessagesSent
            && pred_is_the_owner_of_a_block_share(byz_node, block_share)
        ensures inv_honest_nodes_are_not_owners_of_block_shares_from_adversary_body(dv, block_share)
        {
            forall hn: BLSPubkey | is_an_honest_node(dv, hn)
            ensures !pred_is_the_owner_of_a_block_share(hn, block_share)
            {
                assert hn != byz_node;
                lem_different_signers_cannot_generate_the_same_block_share(
                    byz_node,
                    hn,
                    block_share
                );
                assert !pred_is_the_owner_of_a_block_share(hn, block_share);
            }
        }
    }

    lemma lem_AdversaryTakingStep_block_share_from_honest_node_were_sent_before(
        dv: DVState,        
        event: DV_Block_Proposer_Spec.BlockEvent,
        node: BLSPubkey,
        new_randao_share_sent: set<MessaageWithRecipient<RandaoShare>>, 
        new_block_share_sent: set<MessaageWithRecipient<SignedBeaconBlock>>,
        randaoShareReceivedByTheNode: set<RandaoShare> , 
        blockShareReceivedByTheNode: set<SignedBeaconBlock>,        
        dv': DVState,
        pubkey: BLSPubkey,
        old_block_share: SignedBeaconBlock
    )
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv') 
    requires event.AdversaryTakingStep? 
    requires NextAdversary(dv, node, new_randao_share_sent, new_block_share_sent, randaoShareReceivedByTheNode, blockShareReceivedByTheNode, dv')
    requires inv_all_honest_nodes_is_a_quorum(dv)
    requires is_an_honest_node(dv', pubkey)
    requires && old_block_share in dv'.block_share_network.allMessagesSent
             && pred_is_the_owner_of_a_block_share(pubkey, old_block_share)
    ensures old_block_share in dv.block_share_network.allMessagesSent
    {
        var beacon_block := old_block_share.block;
        var block_signing_root := compute_block_signing_root(beacon_block);
        
        assert  dv'.block_share_network.allMessagesSent
                == 
                dv.block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient(new_block_share_sent);

        assert  || old_block_share in dv.block_share_network.allMessagesSent
                || old_block_share in getMessagesFromMessagesWithRecipient(new_block_share_sent)
                ;

        if old_block_share in getMessagesFromMessagesWithRecipient(new_block_share_sent)
        {
            if new_block_share_sent == {}
            {
                assert {} == getMessagesFromMessagesWithRecipient(new_block_share_sent);
            }
            assert {} != getMessagesFromMessagesWithRecipient(new_block_share_sent);
            var old_block_share_sent :|
                    && old_block_share_sent in new_block_share_sent
                    && old_block_share_sent.message == old_block_share
                    ;
            var signer: BLSPubkey :| verify_bls_signature(block_signing_root, old_block_share.signature, signer);
            assert signer in dv'.adversary.nodes;     
            lem_inv_honest_nodes_are_not_owners_of_block_shares_from_adversary(dv');
            lem_different_signers_cannot_generate_the_same_block_share(
                signer,
                pubkey,
                old_block_share
            );
        }
        assert old_block_share !in getMessagesFromMessagesWithRecipient(new_block_share_sent);
        assert old_block_share in dv.block_share_network.allMessagesSent;
    }

    lemma lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_dv_next_AdversaryTakingStep(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.AdversaryTakingStep?
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_all_honest_nodes_is_a_quorum(dv)
    requires inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(dv)
    requires inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks(dv)
    requires inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(dv)   
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv)
    requires inv_seq_of_proposer_duties_is_ordered(dv)
    ensures  inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv')
    {        
        
        match event 
        {
            case AdversaryTakingStep(node, new_randao_share_sent, new_block_share_sent, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                lem_inv_unchanged_dvc_rs_pubkey_dv_next(dv, event, dv');
        
                forall hn: BLSPubkey, slot: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> | 
                            && is_an_honest_node(dv, hn) 
                            && var dvc' := dv.honest_nodes_states[hn];
                            && slot in dvc'.block_consensus_engine_state.slashing_db_hist.Keys
                            && vp in dvc'.block_consensus_engine_state.slashing_db_hist[slot].Keys
                            && db in dvc'.block_consensus_engine_state.slashing_db_hist[slot][vp]
                ensures inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_body(
                            dv',
                            hn,
                            slot,
                            vp,
                            db
                        )
                {
                    var dvc := dv.honest_nodes_states[hn];
                    var dvc' := dv'.honest_nodes_states[hn];
                    assert dvc == dvc';
                    assert db in dvc.block_consensus_engine_state.slashing_db_hist[slot][vp];

                    assert inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_body(
                            dv,
                            hn,
                            slot, 
                            vp, 
                            db
                        );
                    
                    assert hn == dvc.rs.pubkey;

                    forall block_share: SignedBeaconBlock | 
                            && block_share in dv'.block_share_network.allMessagesSent
                            && is_an_honest_node(dv', hn)
                            && pred_is_the_owner_of_a_block_share(hn, block_share)
                            && block_share.block.slot < slot
                    ensures &&  var beacon_block := block_share.block;
                            &&  var slashing_db_block := construct_SlashingDBBlock_from_beacon_block(beacon_block);
                            && slashing_db_block in db
                    {
                        lem_AdversaryTakingStep_block_share_from_honest_node_were_sent_before(
                            dv,        
                            event,
                            node,
                            new_randao_share_sent,
                            new_block_share_sent,
                            randaoShareReceivedByTheNode,
                            blockShareReceivedByTheNode,
                            dv',
                            hn,
                            block_share
                        );
                        assert block_share in dv.block_share_network.allMessagesSent;

                        var beacon_block := block_share.block;
                        var slashing_db_block := 
                            construct_SlashingDBBlock_from_beacon_block(beacon_block);

                        assert  && block_share in dv.block_share_network.allMessagesSent
                                && is_an_honest_node(dv, hn)
                                && pred_is_the_owner_of_a_block_share(hn, block_share)
                                && block_share.block.slot < slot
                                ;
                        assert slashing_db_block in db;                        
                    }
                    
                }

                assert inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv');
        }  
    }    

    lemma lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_from_dv_to_dvc(
        dv: DVState,
        hn: BLSPubkey
    )
    requires is_an_honest_node(dv, hn)
    requires inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv)
    ensures inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(
                dv.block_share_network.allMessagesSent,
                dv.honest_nodes_states[hn]     
            )
    {
        var allMessagesSent := dv.block_share_network.allMessagesSent;
        var process := dv.honest_nodes_states[hn];

        forall slot: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> | 
                && slot in process.block_consensus_engine_state.slashing_db_hist.Keys
                && vp in process.block_consensus_engine_state.slashing_db_hist[slot].Keys
                && db in process.block_consensus_engine_state.slashing_db_hist[slot][vp]
        ensures inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_body(
                    dv,
                    hn,
                    slot,
                    vp,
                    db)
        {
            var rs_pubkey := process.rs.pubkey;

            forall block_share: SignedBeaconBlock | 
                    && block_share in dv.block_share_network.allMessagesSent
                    && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
                    && block_share.block.slot < slot
            ensures && var beacon_block := block_share.block;
                    && var slashing_db_block := construct_SlashingDBBlock_from_beacon_block(beacon_block);
                    && slashing_db_block in db
            {
                assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body_conclusion(
                            allMessagesSent,
                            rs_pubkey,
                            slot,
                            vp,
                            db,
                            block_share
                        );

                var beacon_block := block_share.block;
                var slashing_db_block := construct_SlashingDBBlock_from_beacon_block(beacon_block);
                assert  slashing_db_block in db;
            }
        }
    }

    lemma lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_ServeProposerDuty(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState,
        node: BLSPubkey, 
        nodeEvent: Types.BlockEvent, 
        nodeOutputs: Outputs,
        proposer_duty: ProposerDuty
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.HonestNodeTakingStep?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires nodeEvent.ServeProposerDuty?
    requires nodeEvent == ServeProposerDuty(proposer_duty)
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_all_honest_nodes_is_a_quorum(dv)
    requires inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(dv)
    requires inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks(dv)
    requires inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(dv)   
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv)
    requires inv_seq_of_proposer_duties_is_ordered(dv)
    ensures  inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv')
    {        
        assert  is_an_honest_node(dv, node);

        var process := dv.honest_nodes_states[node];
        var process' := dv'.honest_nodes_states[node];
        var allMessagesSent := dv.block_share_network.allMessagesSent;

        assert  allMessagesSent == dv'.block_share_network.allMessagesSent;
        assert  inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_helper(dv, node);
        assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(allMessagesSent, process);

        lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_serve_proposer_duty(                            
            process,
            proposer_duty,
            process',
            dv.block_share_network.allMessagesSent
        );

        forall hn: BLSPubkey | is_an_honest_node(dv', hn)
        ensures inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_helper(dv', hn)
        {
            if hn == node
            {
                forall slot: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> | 
                    && slot in process'.block_consensus_engine_state.slashing_db_hist.Keys
                    && vp in process'.block_consensus_engine_state.slashing_db_hist[slot].Keys
                    && db in process'.block_consensus_engine_state.slashing_db_hist[slot][vp]
                ensures inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_body(
                            dv,
                            hn,
                            slot,
                            vp,
                            db)
                {
                    var rs_pubkey := process.rs.pubkey;

                    forall block_share: SignedBeaconBlock | 
                            && block_share in dv'.block_share_network.allMessagesSent
                            && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
                            && block_share.block.slot < slot
                    ensures && var beacon_block := block_share.block;
                            && var slashing_db_block := construct_SlashingDBBlock_from_beacon_block(beacon_block);
                            && slashing_db_block in db
                    {
                        assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body_conclusion(
                                    allMessagesSent,
                                    rs_pubkey,
                                    slot,
                                    vp,
                                    db,
                                    block_share
                                );

                        var beacon_block := block_share.block;
                        var slashing_db_block := construct_SlashingDBBlock_from_beacon_block(beacon_block);
                        assert  slashing_db_block in db;
                    }
                }
            }
            else
            {
                var dvc := dv.honest_nodes_states[hn];
                var dvc' := dv'.honest_nodes_states[hn];
                assert  dvc == dvc';                
            }
        }                                                    
    }

    lemma lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_BlockConsensusDecided(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState,
        node: BLSPubkey, 
        nodeEvent: Types.BlockEvent, 
        nodeOutputs: Outputs,
        id: Slot,
        decided_beacon_block: BeaconBlock
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.HonestNodeTakingStep?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires nodeEvent.BlockConsensusDecided?
    requires nodeEvent == BlockConsensusDecided(id, decided_beacon_block)
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_all_honest_nodes_is_a_quorum(dv)
    requires inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(dv)
    requires inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks(dv)
    requires inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(dv)   
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv)
    requires inv_seq_of_proposer_duties_is_ordered(dv)
    ensures  inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv')
    {        
        var dvc := dv.honest_nodes_states[node];
        var dvc' := dv'.honest_nodes_states[node];
        
        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
        {
            if  && dvc.current_proposer_duty.isPresent()
                && dvc.current_proposer_duty.safe_get().slot == decided_beacon_block.slot
                && id == decided_beacon_block.slot
            {
                var allMessagesSent := dv.block_share_network.allMessagesSent;

                lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_from_dv_to_dvc(
                    dv,
                    node
                );

                assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                            allMessagesSent,
                            dvc
                        );
                
                lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_dv_next(
                    dv,
                    event,
                    dv'
                );

                assert  forall slot | slot in dvc'.block_consensus_engine_state.slashing_db_hist.Keys
                            ::
                            slot <= dvc'.latest_proposer_duty.safe_get().slot
                        ;
                assert  inv_available_current_proposer_duty_is_latest_proposer_duty_body(dvc');

                lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_block_consensus_decided_new_sent_block_shares(                            
                            dvc,
                            id,
                            decided_beacon_block, 
                            dvc',
                            allMessagesSent
                        );
                
                var allMessagesSent' := dv'.block_share_network.allMessagesSent;
                var outputs := f_block_consensus_decided(dvc, id, decided_beacon_block).outputs;
                assert allMessagesSent' == allMessagesSent + getMessagesFromMessagesWithRecipient(outputs.sent_block_shares);

                var new_block_slashing_db := f_update_block_slashing_db(dvc.block_slashing_db, decided_beacon_block);
                var block_signing_root := compute_block_signing_root(decided_beacon_block);
                var fork_version := bn_get_fork_version(decided_beacon_block.slot);
                var block_signature := rs_sign_block(decided_beacon_block, fork_version, block_signing_root, dvc.rs);
                var block_share := SignedBeaconBlock(decided_beacon_block, block_signature);
                var messagesToBeSent := f_block_consensus_decided(dvc, id, decided_beacon_block).outputs.sent_block_shares;

                assert forall m | m in messagesToBeSent :: m.message == block_share; 

                lemmaOnGetMessagesFromMessagesWithRecipientWhenAllMessagesAreTheSame(messagesToBeSent, block_share);    
                assert  getMessagesFromMessagesWithRecipient(messagesToBeSent) ==  {block_share};
                assert  dv'.block_share_network.allMessagesSent 
                        == 
                        dv.block_share_network.allMessagesSent + { block_share }
                        ; 

                forall hn: BLSPubkey, slot: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> | 
                            && is_an_honest_node(dv, hn) 
                            && var process' := dv.honest_nodes_states[hn];
                            && slot in process'.block_consensus_engine_state.slashing_db_hist.Keys
                            && vp in process'.block_consensus_engine_state.slashing_db_hist[slot].Keys
                            && db in process'.block_consensus_engine_state.slashing_db_hist[slot][vp]
                ensures inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_body(
                            dv',
                            hn,
                            slot,
                            vp,
                            db)
                {
                    var process := dv.honest_nodes_states[hn];
                    var process' := dv'.honest_nodes_states[hn];                            
                    assert hn == process.rs.pubkey == process'.rs.pubkey;

                    forall block_share: SignedBeaconBlock | 
                            && block_share in dv'.block_share_network.allMessagesSent
                            && is_an_honest_node(dv', hn)
                            && pred_is_the_owner_of_a_block_share(hn, block_share)
                            && block_share.block.slot < slot
                    ensures && var beacon_block := block_share.block;
                            && var slashing_db_block := construct_SlashingDBBlock_from_beacon_block(beacon_block);
                            && slashing_db_block in db
                    {
                        assert  || block_share in dv.block_share_network.allMessagesSent 
                                || block_share in { block_share }
                                ;
                        if block_share in dv.block_share_network.allMessagesSent
                        {
                            var beacon_block := block_share.block;
                            var slashing_db_block := 
                                construct_SlashingDBBlock_from_beacon_block(beacon_block);

                            assert  && block_share in dv.block_share_network.allMessagesSent
                                    && is_an_honest_node(dv, hn)
                                    && pred_is_the_owner_of_a_block_share(hn, block_share)
                                    && block_share.block.slot < slot
                                    ;
                            assert slashing_db_block in db;                        
                        }
                        else
                        {
                            assert block_share == block_share;

                            var beacon_block := block_share.block;
                            var block_signing_root := compute_block_signing_root(beacon_block);
                            var signer: BLSPubkey :| 
                                    verify_bls_signature(block_signing_root, block_share.signature, signer);

                            assert pred_is_the_owner_of_a_block_share(dvc'.rs.pubkey, block_share);

                            lem_unique_owner_of_block_share(
                                signer,
                                dvc'.rs.pubkey,
                                block_share
                            );
                            assert signer == dvc'.rs.pubkey;
                            if hn == signer
                            {
                                assert ( forall slot: Slot | slot in dvc'.block_consensus_engine_state.slashing_db_hist.Keys ::
                                        block_share.block.slot >= slot
                                );
                            }
                            else
                            {
                                lem_different_signers_cannot_generate_the_same_block_share(
                                    dvc'.rs.pubkey,
                                    hn,
                                    block_share
                                );

                                assert !pred_is_the_owner_of_a_block_share(hn, block_share);
                            }
                        }
                    }
                }
            }
            else
            {
                assert  dvc == dvc';
                assert  dv.block_share_network.allMessagesSent == dv'.block_share_network.allMessagesSent;
                
                forall hn: BLSPubkey | is_an_honest_node(dv', hn) 
                ensures inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_helper(dv', hn)
                {
                    assert  is_an_honest_node(dv, hn);
                    assert  dv.honest_nodes_states[hn] == dv'.honest_nodes_states[hn];
                    assert  inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_helper(dv', hn);
                }

                assert  inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv');
            }

        }                 
        assert inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv');        
    }   

    lemma lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_HonestNodeTakingStep_helper(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState,
        node: BLSPubkey, 
        nodeEvent: Types.BlockEvent, 
        nodeOutputs: Outputs
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.HonestNodeTakingStep?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_all_honest_nodes_is_a_quorum(dv)
    requires inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(dv)
    requires inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks(dv)
    requires inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(dv)   
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv)
    requires inv_seq_of_proposer_duties_is_ordered(dv)
    requires && var dvc':= dv'.honest_nodes_states[node];
             && inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                            dv'.block_share_network.allMessagesSent,
                            dvc'
                        )
    requires dv.block_share_network.allMessagesSent == dv'.block_share_network.allMessagesSent
    ensures  inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv')
    {
        forall hn: BLSPubkey | is_an_honest_node(dv', hn) 
        ensures inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_helper(dv', hn)
        {
            assert  is_an_honest_node(dv, hn);
            var dvc := dv.honest_nodes_states[hn];
            var dvc' := dv'.honest_nodes_states[hn];
            var allMessagesSent := dv.block_share_network.allMessagesSent;
            var allMessagesSent' := dv'.block_share_network.allMessagesSent;

            if hn == node
            {
                var rs_pubkey := dvc.rs.pubkey;
                lem_inv_unchanged_dvc_rs_pubkey_dv_next(dv, event, dv');
                assert  rs_pubkey == dvc'.rs.pubkey;

                forall slot: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> | 
                            && slot in dvc'.block_consensus_engine_state.slashing_db_hist.Keys
                            && vp in dvc'.block_consensus_engine_state.slashing_db_hist[slot].Keys
                            && db in dvc'.block_consensus_engine_state.slashing_db_hist[slot][vp]
                
                {
                    assert  allMessagesSent == allMessagesSent';

                    forall block_share: SignedBeaconBlock | 
                            && block_share in allMessagesSent'
                            && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
                            && block_share.block.slot < slot
                    ensures && var beacon_block := block_share.block;
                            && var slashing_db_block := construct_SlashingDBBlock_from_beacon_block(beacon_block);
                            && slashing_db_block in db
                    {
                        var beacon_block := block_share.block;
                        var slashing_db_block := construct_SlashingDBBlock_from_beacon_block(beacon_block);        
                        assert  slashing_db_block in db;
                    }
                }
            }
            else
            {
                assert  hn != node;
                assert  dvc == dvc';
                assert  allMessagesSent == allMessagesSent';
                assert  inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_helper(dv', hn);
            }
        }
    }

    // lemma lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_ImportedNewBlock(
    //     dv: DVState,
    //     event: DV_Block_Proposer_Spec.BlockEvent,
    //     dv': DVState,
    //     node: BLSPubkey, 
    //     nodeEvent: Types.BlockEvent, 
    //     nodeOutputs: Outputs,
    //     block: BeaconBlock
    // )    
    // requires NextEventPreCond(dv, event)
    // requires NextEvent(dv, event, dv')  
    // requires event.HonestNodeTakingStep?
    // requires event.event.ImportedNewBlock?
    // requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    // requires nodeEvent.ImportedNewBlock?
    // requires nodeEvent == ImportedNewBlock(block)  // Error as duplicated names
    // requires inv_unchanged_dvc_rs_pubkey(dv)
    // requires inv_all_honest_nodes_is_a_quorum(dv)
    // requires inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(dv)
    // requires inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks(dv)
    // requires inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv)
    // requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    // requires inv_available_current_proposer_duty_is_latest_proposer_duty(dv)
    // requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    // requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(dv)   
    // requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv)
    // requires inv_seq_of_proposer_duties_is_ordered(dv)
    // ensures  inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv')
    // {        
    //     var allMessagesSent := dv.block_share_network.allMessagesSent;
    //     var dvc := dv.honest_nodes_states[node];
    //     var dvc' := dv'.honest_nodes_states[node];
    //     var dvc_after_adding_block := f_add_block_to_bn(dvc, nodeEvent.block);

    //     lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_from_dv_to_dvc(
    //                 dv,
    //                 node
    //             );

    //     assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
    //                         allMessagesSent,
    //                         dvc
    //                     );
    //     assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
    //                         allMessagesSent,
    //                         dvc_after_adding_block
    //                     );

    //     lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_listen_for_new_imported_blocks(            
    //         dvc_after_adding_block,
    //         block,
    //         dvc',
    //         dv.block_share_network.allMessagesSent
    //     );

    //     lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_HonestNodeTakingStep_helper(
    //         dv,
    //         event,
    //         dv',
    //         node,
    //         nodeEvent,
    //         nodeOutputs
    //     );

    //     assert inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv');                
    // }

    lemma lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_ImportedNewBlock(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState,
        node: BLSPubkey, 
        nodeEvent: Types.BlockEvent, 
        nodeOutputs: Outputs
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.HonestNodeTakingStep?
    requires event.event.ImportedNewBlock?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires nodeEvent.ImportedNewBlock?
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_all_honest_nodes_is_a_quorum(dv)
    requires inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(dv)
    requires inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks(dv)
    requires inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(dv)   
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv)
    requires inv_seq_of_proposer_duties_is_ordered(dv)
    ensures  inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv')
    {        
        var allMessagesSent := dv.block_share_network.allMessagesSent;
        var dvc := dv.honest_nodes_states[node];
        var dvc' := dv'.honest_nodes_states[node];
        var dvc_after_adding_block := f_add_block_to_bn(dvc, nodeEvent.block);

        lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_from_dv_to_dvc(
                    dv,
                    node
                );

        assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                            allMessagesSent,
                            dvc
                        );
        assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                            allMessagesSent,
                            dvc_after_adding_block
                        );

        match nodeEvent
        {
            case ImportedNewBlock(block) =>
                lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_listen_for_new_imported_blocks(            
                    dvc_after_adding_block,
                    block,
                    dvc',
                    dv.block_share_network.allMessagesSent
                );

                lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_HonestNodeTakingStep_helper(
                    dv,
                    event,
                    dv',
                    node,
                    nodeEvent,
                    nodeOutputs
                );

                assert inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv');                
        }

        

        
    }

    lemma lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_ReceiveSignedBeaconBlock(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState,
        node: BLSPubkey, 
        nodeEvent: Types.BlockEvent, 
        nodeOutputs: Outputs,
        block_share: SignedBeaconBlock
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.HonestNodeTakingStep?
    requires event.event.ReceiveSignedBeaconBlock?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires nodeEvent.ReceiveSignedBeaconBlock?
    requires nodeEvent == ReceiveSignedBeaconBlock(block_share)
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_all_honest_nodes_is_a_quorum(dv)
    requires inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(dv)
    requires inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks(dv)
    requires inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(dv)   
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv)
    requires inv_seq_of_proposer_duties_is_ordered(dv)
    ensures  inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv')
    {                
        var allMessagesSent := dv.block_share_network.allMessagesSent;
        var allMessagesSent' := dv'.block_share_network.allMessagesSent;
        var dvc := dv.honest_nodes_states[node];
        var dvc' := dv'.honest_nodes_states[node];

        assert  allMessagesSent == allMessagesSent';

        lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_from_dv_to_dvc(
                    dv,
                    node
                );

        assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                            allMessagesSent,
                            dvc
                        );
        
        lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_listen_for_block_signature_shares(
            dvc,
            block_share,
            dvc',
            dv.block_share_network.allMessagesSent
        );

        assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                    dv'.block_share_network.allMessagesSent,
                    dvc'
                );

        lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_HonestNodeTakingStep_helper(
            dv,
            event,
            dv',
            node,
            nodeEvent,
            nodeOutputs
        );

        assert  inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv');
    }

    lemma lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_ResendRandaoRevealSignatureShare(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState,
        node: BLSPubkey, 
        nodeEvent: Types.BlockEvent, 
        nodeOutputs: Outputs
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.HonestNodeTakingStep?
    requires event.event.ResendRandaoRevealSignatureShare?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires nodeEvent.ResendRandaoRevealSignatureShare?
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_all_honest_nodes_is_a_quorum(dv)
    requires inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(dv)
    requires inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks(dv)
    requires inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(dv)   
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv)
    requires inv_seq_of_proposer_duties_is_ordered(dv)
    ensures  inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv')
    {                
        var allMessagesSent := dv.block_share_network.allMessagesSent;
        var allMessagesSent' := dv'.block_share_network.allMessagesSent;
        var dvc := dv.honest_nodes_states[node];
        var dvc' := dv'.honest_nodes_states[node];

        assert  allMessagesSent == allMessagesSent';

        lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_from_dv_to_dvc(
                    dv,
                    node
                );

        assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                            allMessagesSent,
                            dvc
                        );
        
        lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_resend_randao_share(
            dvc,
            dvc',
            dv.block_share_network.allMessagesSent
        );

        assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                    dv'.block_share_network.allMessagesSent,
                    dvc'
                );

        lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_HonestNodeTakingStep_helper(
            dv,
            event,
            dv',
            node,
            nodeEvent,
            nodeOutputs
        );

        assert  inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv');
    }

    lemma lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_ResendBlockShare(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState,
        node: BLSPubkey, 
        nodeEvent: Types.BlockEvent, 
        nodeOutputs: Outputs
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.HonestNodeTakingStep?
    requires event.event.ResendBlockShare?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires nodeEvent.ResendBlockShare?
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_all_honest_nodes_is_a_quorum(dv)
    requires inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(dv)
    requires inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks(dv)
    requires inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(dv)   
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv)
    requires inv_seq_of_proposer_duties_is_ordered(dv)
    ensures  inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv')
    {                
        var allMessagesSent := dv.block_share_network.allMessagesSent;
        var allMessagesSent' := dv'.block_share_network.allMessagesSent;
        var dvc := dv.honest_nodes_states[node];
        var dvc' := dv'.honest_nodes_states[node];

        assert  allMessagesSent == allMessagesSent';

        lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_from_dv_to_dvc(
                    dv,
                    node
                );

        assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                            allMessagesSent,
                            dvc
                        );
        
        lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_resend_block_share(
            dvc,
            dvc',
            dv.block_share_network.allMessagesSent
        );

        assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                    dv'.block_share_network.allMessagesSent,
                    dvc'
                );

        lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_HonestNodeTakingStep_helper(
            dv,
            event,
            dv',
            node,
            nodeEvent,
            nodeOutputs
        );

        assert  inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv');
    }

    lemma lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_ReceiveRandaoShare(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState,
        node: BLSPubkey, 
        nodeEvent: Types.BlockEvent, 
        nodeOutputs: Outputs,
        randao_share: RandaoShare
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.HonestNodeTakingStep?
    requires event.event.ReceiveRandaoShare?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires nodeEvent.ReceiveRandaoShare?
    requires nodeEvent == ReceiveRandaoShare(randao_share)
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_all_honest_nodes_is_a_quorum(dv)
    requires inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(dv)
    requires inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks(dv)
    requires inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(dv)   
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv)
    requires inv_seq_of_proposer_duties_is_ordered(dv)
    requires is_an_honest_node(dv, node);
    ensures  inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv')
    {   
        assert is_an_honest_node(dv, node);   
        assert is_an_honest_node(dv', node);       

        var dvc := dv.honest_nodes_states[node];        
        var dvc' := dv'.honest_nodes_states[node];
        var state_and_outputs := f_listen_for_randao_shares(dvc, randao_share);
        assert  && state_and_outputs.state == dvc'
                && state_and_outputs.outputs == getEmptyOuputs()
                ;

        var allMessagesSent := dv.block_share_network.allMessagesSent;
        var allMessagesSent' := dv'.block_share_network.allMessagesSent;
        assert  allMessagesSent == allMessagesSent';
        
        assert inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv);

        lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_from_dv_to_dvc(
            dv,
            node
        );

        assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                            allMessagesSent,
                            dvc
                        );
        
        lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_listen_for_randao_shares(
            dvc,
            randao_share,
            dvc',
            dv.block_share_network.allMessagesSent
        );

        assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                    dv'.block_share_network.allMessagesSent,
                    dvc'
                );

        lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_HonestNodeTakingStep_helper(
            dv,
            event,
            dv',
            node,
            nodeEvent,
            nodeOutputs
        );

        assert  inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv');
    }

    lemma lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_NoEvent(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState,
        node: BLSPubkey, 
        nodeEvent: Types.BlockEvent, 
        nodeOutputs: Outputs
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.HonestNodeTakingStep?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires nodeEvent.NoEvent?
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_all_honest_nodes_is_a_quorum(dv)
    requires inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(dv)
    requires inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks(dv)
    requires inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(dv)   
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv)
    requires inv_seq_of_proposer_duties_is_ordered(dv)
    requires is_an_honest_node(dv, node);
    ensures  inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv')
    {   
        assert is_an_honest_node(dv, node);   
        assert is_an_honest_node(dv', node);       

        var dvc := dv.honest_nodes_states[node];        
        var dvc' := dv'.honest_nodes_states[node];
        assert  dvc == dvc';

        var allMessagesSent := dv.block_share_network.allMessagesSent;
        var allMessagesSent' := dv'.block_share_network.allMessagesSent;
        assert  allMessagesSent == allMessagesSent';
        
        assert inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv);

        lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_from_dv_to_dvc(
            dv,
            node
        );

        assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                            allMessagesSent,
                            dvc
                        );
        
        assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                    dv'.block_share_network.allMessagesSent,
                    dvc'
                );

        lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_HonestNodeTakingStep_helper(
            dv,
            event,
            dv',
            node,
            nodeEvent,
            nodeOutputs
        );

        assert  inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv');
    }

    lemma lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_unchanged_dvc_rs_pubkey(dv)
    requires inv_all_honest_nodes_is_a_quorum(dv)
    requires inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(dv)
    requires inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks(dv)
    requires inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty(dv)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(dv)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist(dv)   
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv)
    requires inv_seq_of_proposer_duties_is_ordered(dv)
    ensures  inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv')
    {        
        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>  
                        lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_ServeProposerDuty(
                            dv,
                            event,
                            dv',
                            node,
                            nodeEvent,
                            nodeOutputs,
                            proposer_duty
                        );

                    case ReceiveRandaoShare(randao_share) =>
                        lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_ReceiveRandaoShare(
                            dv,
                            event,
                            dv',
                            node,
                            nodeEvent,
                            nodeOutputs,
                            randao_share
                        );
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_BlockConsensusDecided(
                            dv,
                            event,
                            dv',
                            node,
                            nodeEvent,
                            nodeOutputs,
                            id,                            
                            decided_beacon_block
                        );
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_ReceiveSignedBeaconBlock(
                            dv,
                            event,
                            dv',
                            node,
                            nodeEvent,
                            nodeOutputs,
                            block_share
                        );

                    case ImportedNewBlock(block) => 
                        lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_ImportedNewBlock(
                            dv,
                            event,
                            dv',
                            node,
                            nodeEvent,
                            nodeOutputs
                        );
                                                
                    case ResendRandaoRevealSignatureShare =>
                        lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_ResendRandaoRevealSignatureShare(
                            dv,
                            event,
                            dv',
                            node,
                            nodeEvent,
                            nodeOutputs
                        );

                    case ResendBlockShare =>
                        lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_ResendBlockShare(
                            dv,
                            event,
                            dv',
                            node,
                            nodeEvent,
                            nodeOutputs
                        );
                        
                    case NoEvent =>                         
                        lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_NoEvent(
                            dv,
                            event,
                            dv',
                            node,
                            nodeEvent,
                            nodeOutputs
                        );

                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                lem_inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_dv_next_AdversaryTakingStep(
                            dv,
                            event,
                            dv'
                        );
        }  
    }    

    lemma lem_inv_block_of_all_created_blocks_is_set_of_decided_values_dv_next(
        dv: DVState
    )    
    requires inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(dv)
    requires inv_blocks_of_in_transit_block_shares_are_decided_values(dv)
    requires inv_all_created_signed_beacon_blocks_are_valid(dv)
    ensures  inv_block_of_all_created_blocks_is_set_of_decided_values(dv)
    {        
        forall complete_block | complete_block in dv.all_blocks_created && is_verified_block_with_pubkey(complete_block, dv.dv_pubkey)
        ensures && var consa := dv.consensus_instances_on_beacon_block[complete_block.block.slot];
                && consa.decided_value.isPresent() 
                && complete_block.block == consa.decided_value.safe_get() 
        {
            var hn: BLSPubkey, block_share: SignedBeaconBlock 
                    :| 
                    inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(dv, hn, block_share, complete_block);

            assert complete_block.block.slot == block_share.block.slot;
            assert  inv_blocks_of_in_transit_block_shares_are_decided_values_body(dv, block_share);
            assert  && dv.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.isPresent()
                    && dv.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.safe_get() == block_share.block
                    ;
        }
    }  

    lemma lem_inv_all_blocks_created_is_monotonic_dv_next(dv: DVState, event: DV_Block_Proposer_Spec.BlockEvent, dv': DVState)    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')     
    ensures dv.all_blocks_created <= dv'.all_blocks_created
    { }

    lemma lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_ImportedNewBlock_helper(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')     
    requires inv_consensus_instance_isConditionForSafetyTrue(dv)
    requires inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(dv)
    requires construct_complete_signed_block_assumptions_helper(
                    dv.construct_complete_signed_block,
                    dv.dv_pubkey,
                    dv.all_nodes
                )
    requires inv_only_dv_construct_complete_signed_block(dv)
    requires inv_in_transit_messages_are_in_allMessagesSent(dv)
    requires inv_all_honest_nodes_is_a_quorum(dv)
    requires inv_rcvd_block_shares_are_in_all_sent_messages(dv)
    requires inv_nodes_in_consensus_instances_are_in_dv(dv)
    requires inv_the_same_node_status_in_dv_and_ci(dv)
    requires inv_only_dv_construct_complete_signing_functions(dv)
    requires inv_blocks_of_in_transit_block_shares_are_decided_values(dv)
    requires inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(dv)
    requires inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(dv)
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(dv)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(dv)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(dv)
    requires inv_all_created_signed_beacon_blocks_are_valid(dv)
    requires inv_block_of_all_created_blocks_is_set_of_decided_values(dv)
    ensures inv_block_of_all_created_blocks_is_set_of_decided_values(dv')
    {
        lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_dv_next(dv, event, dv');
        lem_inv_blocks_of_in_transit_block_shares_are_decided_values_dv_next(dv, event, dv');
        lem_inv_all_created_signed_beacon_blocks_are_valid_dv_next(dv, event, dv');
        lem_inv_block_of_all_created_blocks_is_set_of_decided_values_dv_next(dv');
    }

    // lemma lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_checking_processes(
    //     dv: DVState,
    //     event: DV_Block_Proposer_Spec.BlockEvent,
    //     dv': DVState,
    //     node: BLSPubkey,
    //     nodeEvent: Types.BlockEvent,
    //     nodeOutputs: Outputs,
    //     block: BeaconBlock
    // )
    // requires NextEventPreCond(dv, event)
    // requires NextEvent(dv, event, dv')    
    // requires event.HonestNodeTakingStep?
    // requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    // requires nodeEvent.ImportedNewBlock?
    // requires nodeEvent == ImportedNewBlock(block)
    // ensures && var process := dv.honest_nodes_states[node];
    //         && var process' := dv'.honest_nodes_states[node];
    //         &&  var process_after_adding_block := f_add_block_to_bn(process, nodeEvent.block);
    //         && process' == f_listen_for_new_imported_blocks(process_after_adding_block, block).state ; 
    // {
    //     var process := dv.honest_nodes_states[node];
    //     var process' := dv'.honest_nodes_states[node];
    //     var process_after_adding_block := f_add_block_to_bn(process, nodeEvent.block);

    //     assert process' == f_listen_for_new_imported_blocks(process_after_adding_block, block).state ;
    // }

    lemma lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_checking_processes(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState,
        node: BLSPubkey,
        nodeEvent: Types.BlockEvent,
        nodeOutputs: Outputs
    )
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires event.HonestNodeTakingStep?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires nodeEvent.ImportedNewBlock?
    ensures && var process := dv.honest_nodes_states[node];
            && var process' := dv'.honest_nodes_states[node];
            && var process_after_adding_block := f_add_block_to_bn(process, nodeEvent.block);
            && process' == f_listen_for_new_imported_blocks(process_after_adding_block, nodeEvent.block).state ; 
    {
        var process := dv.honest_nodes_states[node];
        var process' := dv'.honest_nodes_states[node];
        var process_after_adding_block := f_add_block_to_bn(process, nodeEvent.block);

        match nodeEvent
        {
            case ImportedNewBlock(block) =>
                assert process' == f_listen_for_new_imported_blocks(process_after_adding_block, block).state ;
        }
    }

    

    lemma lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_ImportedNewBlock(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState,
        node: BLSPubkey,
        nodeEvent: Types.BlockEvent,
        nodeOutputs: Outputs
    )
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')     
    requires event.HonestNodeTakingStep?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires nodeEvent.ImportedNewBlock?
    requires inv_consensus_instance_isConditionForSafetyTrue(dv)
    requires inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(dv)
    requires construct_complete_signed_block_assumptions_helper(
                    dv.construct_complete_signed_block,
                    dv.dv_pubkey,
                    dv.all_nodes
                )
    requires inv_only_dv_construct_complete_signed_block(dv)
    requires inv_in_transit_messages_are_in_allMessagesSent(dv)
    requires inv_all_honest_nodes_is_a_quorum(dv)
    requires inv_rcvd_block_shares_are_in_all_sent_messages(dv)
    requires inv_nodes_in_consensus_instances_are_in_dv(dv)
    requires inv_the_same_node_status_in_dv_and_ci(dv)
    requires inv_only_dv_construct_complete_signing_functions(dv)
    requires inv_blocks_of_in_transit_block_shares_are_decided_values(dv)
    requires inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(dv)
    requires inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(dv)
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(dv)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(dv)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(dv)
    requires inv_all_created_signed_beacon_blocks_are_valid(dv)
    requires inv_block_of_all_created_blocks_is_set_of_decided_values(dv)
    requires inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, event.node, dv.honest_nodes_states[event.node])
    requires inv_block_of_all_created_blocks_is_set_of_decided_values(dv)
    ensures inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv', event.node, dv'.honest_nodes_states[event.node]); 
    {
        var process := dv.honest_nodes_states[node];
        var process' := dv'.honest_nodes_states[node];
        var process_after_adding_block := f_add_block_to_bn(process, nodeEvent.block);

        lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_checking_processes(
            dv,
            event,
            dv',
            node,
            nodeEvent,
            nodeOutputs
        );

        match nodeEvent
        {
            case ImportedNewBlock(block) =>
                assert process' == f_listen_for_new_imported_blocks(process_after_adding_block, block).state ;

                lem_inv_decisions_of_consensus_instances_are_unchanged(dv, event, dv');
                assert  inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv', node, process);
                
                var complete_signed_block: SignedBeaconBlock :|
                            && complete_signed_block in dv.all_blocks_created
                            && complete_signed_block.block == block
                            ;

                lem_inv_all_blocks_created_is_monotonic_dv_next(dv, event, dv');
                assert  complete_signed_block in dv'.all_blocks_created;

                lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_ImportedNewBlock_helper(dv, event, dv');
                assert  inv_block_of_all_created_blocks_is_set_of_decided_values(dv');

                var consa' := dv'.consensus_instances_on_beacon_block[complete_signed_block.block.slot];
                assert  && consa'.decided_value.isPresent() 
                        && complete_signed_block.block == consa'.decided_value.safe_get() 
                        ;
                
                var slot: Slot := block.slot;
                assert  block
                        ==
                        dv'.consensus_instances_on_beacon_block[slot].decided_value.safe_get()
                        ;

                lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body_f_add_block_to_bn(
                    process,
                    block,
                    process_after_adding_block,
                    dv', 
                    node
                );
                
                // assert inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(s', node, s_node2);                     
                // assert  && s'.consensus_instances_on_beacon_block[block.slot].decided_value.isPresent()
                //         && block == s'.consensus_instances_on_beacon_block[block.slot].decided_value.safe_get()
                //         ;

                lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body_f_listen_for_new_imported_blocks(
                    process_after_adding_block,
                    block,
                    process',
                    dv', 
                    node
                );  
                // assert  inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(s', node, process');          
                // assert  node == event.node;
                // assert  process' == s'.honest_nodes_states[event.node];
                assert  inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv', event.node, dv'.honest_nodes_states[event.node]);         
        }                           
    }     

    lemma lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_HonestNodeTakingStep_helper(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState,
        node: BLSPubkey,
        nodeEvent: Types.BlockEvent,
        nodeOutputs: Outputs
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')     
    requires event.HonestNodeTakingStep?
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s)
    requires inv_blocks_of_in_transit_block_shares_are_decided_values(s)               
    requires inv_consensus_instance_isConditionForSafetyTrue(s) 
    requires lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_new_precond(s)  
    requires inv_block_of_all_created_blocks_is_set_of_decided_values(s)
    requires inv_all_created_signed_beacon_blocks_are_valid(s)
    requires construct_complete_signed_block_assumptions_helper(
                    s.construct_complete_signed_block,
                    s.dv_pubkey,
                    s.all_nodes
                )
    requires inv_only_dv_construct_complete_signed_block(s)
    requires inv_in_transit_messages_are_in_allMessagesSent(s)
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_rcvd_block_shares_are_in_all_sent_messages(s)
    requires inv_nodes_in_consensus_instances_are_in_dv(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires inv_only_dv_construct_complete_signing_functions(s)
    requires inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s)
    requires inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(s)
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    requires inv_all_created_signed_beacon_blocks_are_valid(s)
    requires inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(s, event.node, s.honest_nodes_states[event.node])
    ensures inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(s', event.node, s'.honest_nodes_states[event.node]); 
    {
        var s_node := s.honest_nodes_states[node];
        var s'_node := s'.honest_nodes_states[node];

        lem_inv_decisions_of_consensus_instances_are_unchanged(s, event, s');
        assert  inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(s', node, s_node);

        match nodeEvent
        {
            case ServeProposerDuty(proposer_duty) => 
                lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body_f_serve_proposer_duty(
                    s_node,
                    proposer_duty,
                    s'_node,
                    s', 
                    node
                );
                assert inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(s', node, s'_node);

                case ReceiveRandaoShare(randao_share) =>
                lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body_f_listen_for_randao_shares(
                    s_node,
                    randao_share,
                    s'_node,
                    s', 
                    node
                ); 
                assert inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(s', node, s'_node);
        
            case BlockConsensusDecided(id, decided_proposer_data) =>  
                lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body_f_block_consensus_decided(
                    s_node,
                    id,
                    decided_proposer_data,
                    s'_node,
                    s', 
                    node
                ); 
                assert inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(s', node, s'_node);                        
            
            case ReceiveSignedBeaconBlock(block_share) =>
                lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body_f_listen_for_block_signature_shares(
                    s_node,
                    block_share,
                    s'_node,
                    s', 
                    node
                ); 
                assert inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(s', node, s'_node);  
                
            case ImportedNewBlock(block) => 
                lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_ImportedNewBlock(
                    s,
                    event,
                    s',
                    node,
                    nodeEvent,
                    nodeOutputs
                );
                assert inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(s', node, s'_node);                     
            
            case ResendRandaoRevealSignatureShare =>
                assert  s_node.future_consensus_instances_on_blocks_already_decided 
                        == 
                        s'_node.future_consensus_instances_on_blocks_already_decided
                        ;
                assert inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(s', node, s'_node);  

            case ResendBlockShare =>
                assert  s_node.future_consensus_instances_on_blocks_already_decided 
                        == 
                        s'_node.future_consensus_instances_on_blocks_already_decided
                        ;
                assert inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(s', node, s'_node);  

            case NoEvent => 
                assert  s_node == s'_node;
                assert inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(s', node, s'_node);                          
        }        
    }     

    lemma lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_new_precond(s)
    requires inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s)
    requires inv_blocks_of_in_transit_block_shares_are_decided_values(s)               
    requires inv_consensus_instance_isConditionForSafetyTrue(s) 
    requires lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_new_precond(s)  
    requires inv_block_of_all_created_blocks_is_set_of_decided_values(s)
    requires inv_all_created_signed_beacon_blocks_are_valid(s)
    requires construct_complete_signed_block_assumptions_helper(
                    s.construct_complete_signed_block,
                    s.dv_pubkey,
                    s.all_nodes
                )
    requires inv_only_dv_construct_complete_signed_block(s)
    requires inv_in_transit_messages_are_in_allMessagesSent(s)
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_rcvd_block_shares_are_in_all_sent_messages(s)
    requires inv_nodes_in_consensus_instances_are_in_dv(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires inv_only_dv_construct_complete_signing_functions(s)
    requires inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s)
    requires inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(s)
    requires inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)
    requires inv_all_created_signed_beacon_blocks_are_valid(s)
    requires inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums(s)
    ensures inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums(s')
    {
        assert s.block_share_network.allMessagesSent <= s'.block_share_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_HonestNodeTakingStep_helper(s, event, s', node, nodeEvent, nodeOutputs);
                   
                forall hn | hn in s'.honest_nodes_states.Keys   
                ensures inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];

                        var n_state := s.honest_nodes_states[hn];
                        var n_state' := s'.honest_nodes_states[hn];
                        forall slot | slot in n_state'.future_consensus_instances_on_blocks_already_decided.Keys
                        ensures && s'.consensus_instances_on_beacon_block[slot].decided_value.isPresent()
                                && n_state'.future_consensus_instances_on_blocks_already_decided[slot] == s'.consensus_instances_on_beacon_block[slot].decided_value.safe_get()
                        {
                            assert  && s.consensus_instances_on_beacon_block[slot].decided_value.isPresent()
                                    && n_state.future_consensus_instances_on_blocks_already_decided[slot] == s.consensus_instances_on_beacon_block[slot].decided_value.safe_get();
                            
                            assert  n_state.future_consensus_instances_on_blocks_already_decided[slot]
                                    ==
                                    n_state'.future_consensus_instances_on_blocks_already_decided[slot];

                            lem_inv_unchanged_decision_dv(
                                s,
                                event,
                                s',
                                slot
                            );

                            assert  && s'.consensus_instances_on_beacon_block[slot].decided_value.isPresent()
                                    && s'.consensus_instances_on_beacon_block[slot].decided_value.safe_get() == s.consensus_instances_on_beacon_block[slot].decided_value.safe_get();
                        }
                    }
                    else
                    {
                        lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_HonestNodeTakingStep_helper(s, event, s', node, nodeEvent, nodeOutputs);
                    }
                }  
                assert inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums(s');
                         
            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                forall hn | hn in s'.honest_nodes_states.Keys   
                ensures inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                }  
                assert inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums(s');
        }
    }  

   

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_HonestNodeTakingStep_helper(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')     
    requires inv_slots_in_future_decided_beacon_blocks_are_correct(s)
    requires event.HonestNodeTakingStep?
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(s'.honest_nodes_states[event.node])
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
                        lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_serve_proposer_duty(
                            s_node,
                            proposer_duty,
                            s'_node
                        );
                        

                    case ReceiveRandaoShare(randao_share) =>
                        lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_listen_for_randao_shares(s_node, randao_share, s'_node);
                
                    case BlockConsensusDecided(id, decided_proposer_data) =>  
                        lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_block_consensus_decided(
                            s_node,
                            id,
                            decided_proposer_data,
                            s'_node
                        ); 
                   
                    case ReceiveSignedBeaconBlock(block_share) =>
                        lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_listen_for_block_signature_shares(
                            s_node, 
                            block_share, 
                            s'_node
                        );
                        

                    case ImportedNewBlock(block) => 
                        var s_node2 := f_add_block_to_bn(s_node, nodeEvent.block);
                        lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node
                        );  
                    
                 
                    case ResendRandaoRevealSignatureShare =>
                        lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_resend_randao_share(
                            s_node,
                            s'_node
                        );

                    case ResendBlockShare =>
                        lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_resend_block_share(
                            s_node,
                            s'_node
                        );

                    case NoEvent => 
                        assert inv_slots_in_future_decided_beacon_blocks_are_correct_body(s'_node);                          
                }
        }
    }     

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_dv_next(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_slots_in_future_decided_beacon_blocks_are_correct(s)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct(s')  
    {
        assert s.block_share_network.allMessagesSent <= s'.block_share_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_slots_in_future_decided_beacon_blocks_are_correct_HonestNodeTakingStep_helper(s, event, s');
                   
                forall hn | hn in s'.honest_nodes_states.Keys   
                ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(s'.honest_nodes_states[hn]); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                    }
                }  
                assert inv_slots_in_future_decided_beacon_blocks_are_correct(s');
                         
            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                forall hn | hn in s'.honest_nodes_states.Keys   
                ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(s'.honest_nodes_states[hn]); 
                {
                    assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                }  
                assert inv_slots_in_future_decided_beacon_blocks_are_correct(s');
        }
    }      

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_HonestNodeTakingStep(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState,
        node: BLSPubkey,
        nodeEvent: Types.BlockEvent,
        nodeOutputs: Outputs
    )       
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv') 
    requires event.HonestNodeTakingStep? 
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires inv_all_honest_nodes_is_a_quorum(dv)
    requires inv_nodes_in_consensus_instances_are_in_dv(dv)
    requires inv_only_dv_construct_complete_signing_functions(dv)
    requires inv_block_shares_to_broadcast_are_sent_messages(dv)    
    ensures inv_block_shares_to_broadcast_are_sent_messages(dv')
    {
        lem_inv_all_honest_nodes_is_a_quorum_dv_next(dv, event, dv');
        lem_inv_nodes_in_consensus_instances_are_in_dv_dv_next(dv, event, dv');
        lem_inv_only_dv_construct_complete_signing_functions_dv_next(dv, event, dv');

        assert && inv_all_honest_nodes_is_a_quorum(dv')
               && inv_nodes_in_consensus_instances_are_in_dv(dv')
               && inv_only_dv_construct_complete_signing_functions(dv');
        
        
        var dvc := dv.honest_nodes_states[node];
        var dvc' := dv'.honest_nodes_states[node];
        assert  && dvc.peers == dvc'.peers
                && |dvc.peers| > 0 ;

        match nodeEvent
        {
            case ServeProposerDuty(proposer_duty) =>     
                lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_serve_proposer_duty(dvc, proposer_duty, dvc'); 
                assert inv_block_shares_to_broadcast_are_sent_messages(dv');

            case ReceiveRandaoShare(randao_share) =>                         
                lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_listen_for_randao_shares(dvc, randao_share, dvc');                           
                assert inv_block_shares_to_broadcast_are_sent_messages(dv');

            case BlockConsensusDecided(id, decided_beacon_block) => 
                var block_share_network := dv.block_share_network;
                var block_share_network' := dv'.block_share_network;
                if id == decided_beacon_block.slot
                {
                    lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc', nodeOutputs);   
                    assert  block_share_network'.allMessagesSent
                            == 
                            block_share_network.allMessagesSent + getMessagesFromMessagesWithRecipient(nodeOutputs.sent_block_shares)
                            ;               
                    assert inv_block_shares_to_broadcast_are_sent_messages(dv');
                }
                                        
            case ReceiveSignedBeaconBlock(block_share) =>                         
                lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_listen_for_block_signature_shares(dvc, block_share, dvc');   
                assert inv_block_shares_to_broadcast_are_sent_messages(dv');                                             

            case ImportedNewBlock(block) => 
                var dvc_mod := f_add_block_to_bn(dvc, block);
                lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_add_block_to_bn(dvc, block, dvc_mod);
                lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                                                
                assert inv_block_shares_to_broadcast_are_sent_messages(dv');

            case ResendRandaoRevealSignatureShare =>
                lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_resend_randao_share(dvc, dvc');
                assert inv_block_shares_to_broadcast_are_sent_messages(dv');

            case ResendBlockShare =>                         
                lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_resend_block_share(dvc, dvc');
                assert inv_block_shares_to_broadcast_are_sent_messages(dv');

            case NoEvent => 
                assert inv_block_shares_to_broadcast_are_sent_messages(dv');
        }
    }

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )       
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_all_honest_nodes_is_a_quorum(dv)
    requires inv_nodes_in_consensus_instances_are_in_dv(dv)
    requires inv_only_dv_construct_complete_signing_functions(dv)
    requires inv_block_shares_to_broadcast_are_sent_messages(dv)    
    ensures inv_block_shares_to_broadcast_are_sent_messages(dv')
    {   
        lem_inv_all_honest_nodes_is_a_quorum_dv_next(dv, event, dv');
        lem_inv_nodes_in_consensus_instances_are_in_dv_dv_next(dv, event, dv');
        lem_inv_only_dv_construct_complete_signing_functions_dv_next(dv, event, dv');

        assert && inv_all_honest_nodes_is_a_quorum(dv')
               && inv_nodes_in_consensus_instances_are_in_dv(dv')
               && inv_only_dv_construct_complete_signing_functions(dv');
        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                lem_inv_block_shares_to_broadcast_are_sent_messages_HonestNodeTakingStep(
                    dv,
                    event,
                    dv',
                    node,
                    nodeEvent,
                    nodeOutputs
                ); 

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                assert inv_block_shares_to_broadcast_are_sent_messages(dv');
                
        }        
    }

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_stored_SlashingDBBlocks_have_available_signing_root(dv)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var process := dv.honest_nodes_states[node];
                var process' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_serve_proposer_duty(process, proposer_duty, process');
                    
                    case ReceiveRandaoShare(randao_share) =>
                        lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_listen_for_randao_shares(process, randao_share, process');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(process, id, decided_beacon_block)
                        {
                            lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_block_consensus_decided(process, id, decided_beacon_block, process');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_listen_for_block_signature_shares(process, block_share, process');                        
   
                    case ImportedNewBlock(block) => 
                        var process := f_add_block_to_bn(process, nodeEvent.block);
                        lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_listen_for_new_imported_blocks(process, block, process');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    } 

    lemma lem_inv_at_most_one_submitted_signed_beacon_block_with_an_available_signing_root_for_every_slot_dv_next(
        dv: DVState
    )    
    requires inv_block_of_all_created_blocks_is_set_of_decided_values(dv)
    ensures inv_at_most_one_submitted_signed_beacon_block_with_an_available_signing_root_for_every_slot(dv)
    {
        forall sbb1, sbb2: SignedBeaconBlock |
            && sbb1 in dv.all_blocks_created
            && sbb2 in dv.all_blocks_created
            && sbb1.block.slot == sbb2.block.slot
        ensures && var bb1 := sbb1.block;
                && var bb2 := sbb2.block;
                && var sdbb1 := construct_SlashingDBBlock_from_beacon_block(bb1);
                && var sdbb2 := construct_SlashingDBBlock_from_beacon_block(bb2);
                && sdbb1.signing_root.isPresent()
                && sdbb2.signing_root.isPresent()
                && sdbb1.signing_root.safe_get() == sdbb2.signing_root.safe_get()
        {
            var k: Slot := sbb1.block.slot;
            assert  k == sbb2.block.slot;

            var bb1 := sbb1.block;            
            var bb2 := sbb2.block;            

            
            
            assert  dv.consensus_instances_on_beacon_block[k].decided_value.isPresent();

            var beacon_block := dv.consensus_instances_on_beacon_block[k].decided_value.safe_get();

            calc {
                bb1;  
                ==
                beacon_block;
                ==
                bb2;
            }
        }
    }
        
    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_available_current_proposer_duty_is_latest_proposer_duty(dv)
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db(dv)
    requires inv_slots_in_future_decided_beacon_blocks_are_correct(dv)
    requires inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty(dv)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty(dv)
    requires inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty(dv)
    ensures inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var process := dv.honest_nodes_states[node];
                var process' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_serve_proposer_duty(process, proposer_duty, process');
                    
                    case ReceiveRandaoShare(randao_share) =>
                        lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_listen_for_randao_shares(process, randao_share, process');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(process, id, decided_beacon_block)
                        {
                            lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_block_consensus_decided(process, id, decided_beacon_block, process');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_listen_for_block_signature_shares(process, block_share, process');                        
   
                    case ImportedNewBlock(block) => 
                        var process := f_add_block_to_bn(process, nodeEvent.block);
                        lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_listen_for_new_imported_blocks(process, block, process');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    } 

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty(dv)
    requires inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty(dv)
    requires inv_slots_in_future_decided_beacon_blocks_are_correct(dv)
    requires inv_current_proposer_duty_is_either_none_or_latest_proposer_duty(dv)
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db(dv)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var process := dv.honest_nodes_states[node];
                var process' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_serve_proposer_duty(process, proposer_duty, process');
                    
                    case ReceiveRandaoShare(randao_share) =>
                        lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_listen_for_randao_shares(process, randao_share, process');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(process, id, decided_beacon_block)
                        {
                            lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_block_consensus_decided(process, id, decided_beacon_block, process');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_listen_for_block_signature_shares(process, block_share, process');                        
   
                    case ImportedNewBlock(block) => 
                        var process := f_add_block_to_bn(process, nodeEvent.block);
                        lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_listen_for_new_imported_blocks(process, block, process');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    } 

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db(dv)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var process := dv.honest_nodes_states[node];
                var process' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_serve_proposer_duty(process, proposer_duty, process');
                    
                    case ReceiveRandaoShare(randao_share) =>
                        lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_listen_for_randao_shares(process, randao_share, process');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(process, id, decided_beacon_block)
                        {
                            lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_block_consensus_decided(process, id, decided_beacon_block, process');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_listen_for_block_signature_shares(process, block_share, process');                        
   
                    case ImportedNewBlock(block) => 
                        var process := f_add_block_to_bn(process, nodeEvent.block);
                        lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_listen_for_new_imported_blocks(process, block, process');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    } 

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty(dv)
    requires inv_slots_in_future_decided_beacon_blocks_are_correct(dv)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty(dv)
    requires inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty(dv)
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db(dv)
    requires inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block(dv)
    ensures inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var process := dv.honest_nodes_states[node];
                var process' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_serve_proposer_duty(process, proposer_duty, process');
                    
                    case ReceiveRandaoShare(randao_share) =>
                        lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_listen_for_randao_shares(process, randao_share, process');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(process, id, decided_beacon_block)
                        {
                            lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_block_consensus_decided(process, id, decided_beacon_block, process');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_listen_for_block_signature_shares(process, block_share, process');                        
   
                    case ImportedNewBlock(block) => 
                        var process := f_add_block_to_bn(process, nodeEvent.block);
                        lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_listen_for_new_imported_blocks(process, block, process');                        
                                                
                    case ResendRandaoRevealSignatureShare =>
                        lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_resend_randao_share(process, process');

                    case ResendBlockShare =>
                        lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_resend_block_share(process, process');
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    } 
}