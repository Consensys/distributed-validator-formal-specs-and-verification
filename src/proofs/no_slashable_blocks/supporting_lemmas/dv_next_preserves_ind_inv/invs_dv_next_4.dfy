include "../../../../common/commons.dfy"
include "invs_fnc_1.dfy"
include "invs_fnc_2.dfy"


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
include "invs_dv_next_3.dfy"


module Invs_DV_Next_4
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
    import opened Invs_DV_Next_3

    lemma lem_inv_monotonic_block_share_network_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )       
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    ensures dv.block_share_network.allMessagesSent <= dv'.block_share_network.allMessagesSent
    {}

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_ReceiveSignedBeaconBlock_helper1<T>(
        S1: set<T>,
        S2: set<T>,
        S3: set<T>, 
        S4: set<T>
    )
    requires S1 <= S2
    requires S2 <= S3
    requires S3 <= S4
    ensures S1 <= S4
    {}

     lemma lem_inv_rcvd_block_shares_are_from_sent_messages_ReceiveSignedBeaconBlock_helper2<T>(
        S1: set<T>,
        t: T,
        S3: set<T>
    )
    requires S1 <= { t }
    requires t in S3
    ensures S1 <= S3
    {
        lemmaFromMemberToSingletonSet(t, S3);
        assert { t } <= S3;

        lemmaSubsetOfSubset(S1, { t }, S3);        
    }

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_dv_next_helper3<T>(
        S1: set<T>,
        S2: set<T>,
        t: T, 
        S4: set<T>,
        S5: set<T>
    )
    requires S1 <= S2 + { t }
    requires S2 <= S4
    requires t in S5
    requires S4 <= S5
    ensures S1 <= S5
    {
        lemmaSubsetOfSubset(S2, S4, S5);
        assert  S2 <= S5;

        lemmaFromMemberToSingletonSet(t, S5);
        assert { t } <= S5;

        lemmaUnionOfSubsets(S2, { t }, S5);
        assert  S2 + { t } <= S5;
        
        lemmaSubsetOfSubset(S1, S2 + { t }, S5);
    }

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_ReceiveSignedBeaconBlock(
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
    requires event == HonestNodeTakingStep(node, nodeEvent, nodeOutputs)
    requires nodeEvent.ReceiveSignedBeaconBlock?
    requires nodeEvent == ReceiveSignedBeaconBlock(block_share)
    requires inv_all_in_transit_messages_were_sent(dv)
    requires inv_rcvd_block_shares_are_from_sent_messages(dv)
    ensures inv_rcvd_block_shares_are_from_sent_messages(dv')
    {        
        var dvc := dv.honest_nodes_states[node];
        var dvc' := dv'.honest_nodes_states[node];
                
        assert NetworkSpec.Next(dv.block_share_network, dv'.block_share_network, node, nodeOutputs.sent_block_shares, {block_share});
        assert multiset(addReceipientToMessages<SignedBeaconBlock>({block_share}, node)) <= dv.block_share_network.messagesInTransit;
        assert MessaageWithRecipient(message := block_share, receipient := node) in dv.block_share_network.messagesInTransit;        
        assert block_share in dv.block_share_network.allMessagesSent;
        assert block_share in dv'.block_share_network.allMessagesSent;
        
        lem_inv_monotonic_block_share_network_dv_next(dv, event, dv');
        assert dv.block_share_network.allMessagesSent <= dv'.block_share_network.allMessagesSent;
        
        lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_listen_for_block_signature_shares(dvc, block_share, dvc');  

        assert dvc' == f_listen_for_block_signature_shares(dvc, block_share).state;

        var slot := block_share.block.slot;
        var data := block_share.block;
        forall i, j | && i in dvc'.rcvd_block_shares.Keys 
                        && j in dvc'.rcvd_block_shares[i].Keys
        ensures dvc'.rcvd_block_shares[i][j] <= dv'.block_share_network.allMessagesSent;
        {
            if ( || i != slot
                    || j != data
                )
            {             
                lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_listen_for_block_signature_shares_domain(
                    dvc,
                    block_share,
                    dvc'
                );
                assert && i in dvc.rcvd_block_shares.Keys 
                       && j in dvc.rcvd_block_shares[i].Keys;
                assert dvc'.rcvd_block_shares[i][j] <= dvc.rcvd_block_shares[i][j];                                
                assert dvc.rcvd_block_shares[i][j] <= dv.block_share_network.allMessagesSent;
                assert dv.block_share_network.allMessagesSent <= dv'.block_share_network.allMessagesSent;

                lem_inv_rcvd_block_shares_are_from_sent_messages_ReceiveSignedBeaconBlock_helper1(
                    dvc'.rcvd_block_shares[i][j],
                    dvc.rcvd_block_shares[i][j],
                    dv.block_share_network.allMessagesSent,
                    dv'.block_share_network.allMessagesSent
                );

                assert dvc'.rcvd_block_shares[i][j] <= dv'.block_share_network.allMessagesSent;
            }
            else
            {
                if  && i == block_share.block.slot
                    && j == data
                    && ( || i !in dvc.rcvd_block_shares.Keys
                            || j !in dvc.rcvd_block_shares[i].Keys
                        )                                       
                {
                    assert dvc'.rcvd_block_shares[i][j] <= { block_share };
                    assert block_share in dv'.block_share_network.allMessagesSent;

                    lem_inv_rcvd_block_shares_are_from_sent_messages_ReceiveSignedBeaconBlock_helper2(
                        dvc'.rcvd_block_shares[i][j],
                        block_share,
                        dv'.block_share_network.allMessagesSent
                    );

                    assert dvc'.rcvd_block_shares[i][j] <= dv'.block_share_network.allMessagesSent;                                    
                }
                else
                {
                    assert  && i == block_share.block.slot
                            && j == data
                            && i in dvc.rcvd_block_shares.Keys 
                            && j in dvc.rcvd_block_shares[i].Keys
                            ;

                    assert  dvc'.rcvd_block_shares[i][j] 
                            <= 
                            dvc.rcvd_block_shares[i][j] + {block_share}
                            ; 

                    assert  dvc.rcvd_block_shares[i][j]
                            <= 
                            dv.block_share_network.allMessagesSent
                            ; 

                    assert dv.block_share_network.allMessagesSent <= dv'.block_share_network.allMessagesSent;

                    assert block_share in dv'.block_share_network.allMessagesSent;       

                    lem_inv_rcvd_block_shares_are_from_sent_messages_dv_next_helper3(
                        dvc'.rcvd_block_shares[i][j],
                        dvc.rcvd_block_shares[i][j],
                        block_share,
                        dv.block_share_network.allMessagesSent,
                        dv'.block_share_network.allMessagesSent
                    );                             

                    assert dvc'.rcvd_block_shares[i][j] <= dv'.block_share_network.allMessagesSent;                                                                         
                }
            }
        }
        assert inv_rcvd_block_shares_are_from_sent_messages(dv');
    }  

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )       
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_all_in_transit_messages_were_sent(dv)
    requires inv_rcvd_block_shares_are_from_sent_messages(dv)
    ensures inv_rcvd_block_shares_are_from_sent_messages(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_serve_proposer_duty(dvc, proposer_duty, dvc');                        
                    
                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_listen_for_randao_shares(dvc, randao_share, dvc');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');                        

                    case ReceiveSignedBeaconBlock(block_share) =>    
                        lem_inv_rcvd_block_shares_are_from_sent_messages_ReceiveSignedBeaconBlock(
                            dv,
                            event,
                            dv',
                            node,
                            nodeEvent,
                            nodeOutputs,
                            block_share
                        );

                    case ImportedNewBlock(block) => 
                        var dvc_mod := f_add_block_to_bn(dvc, block);
                        lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_add_block_to_bn(dvc, block, dvc_mod);
                        lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                                                
                                                
                    case ResendRandaoRevealSignatureShare =>
                        lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_resend_randao_share(dvc, dvc');
                    
                    case ResendBlockShare =>                  
                        lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_resend_block_share(dvc, dvc');

                    case NoEvent => 
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }        
    }  

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_latest_served_duty_is_a_rcvd_duty(dv)
    requires inv_seq_of_proposer_duties_is_ordered(dv)
    requires inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none(dv)
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty(dv)  
    requires inv_available_current_proposer_duty_is_latest_proposer_duty(dv)
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty(dv)
    requires inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty(dv)    
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>   
                        assert inv_latest_served_duty_is_a_rcvd_duty_body(dvc);                
                        assert inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty_body(dvc, proposer_duty);
                        assert inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(dvc);
                        assert inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(dvc);                                           
                        lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_serve_proposer_duty(dvc, proposer_duty, dvc');
                        assert inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(dvc');
                    
                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_listen_for_randao_shares(dvc, randao_share, dvc');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            assert inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(dvc);
                            lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');
                            assert inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(dvc');
                        }
                    
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_listen_for_block_signature_shares(dvc, block_share, dvc');                        
                       
                    case ImportedNewBlock(block) => 
                        assert inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(dvc);
                        
                        var dvc_mod := f_add_block_to_bn(dvc, block);
                        lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(dvc_mod);
                        lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(dvc_mod);
                        lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(dvc');

                    case ResendRandaoRevealSignatureShare =>                 

                    case ResendBlockShare =>                                                     

                    case NoEvent => 
                        
                }
                
            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    } 

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty(dv)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty(dv')
    {  
        assert inv_unchanged_dv_seq_of_proposer_duties(dv, dv');

        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>    
                        assert  dv'.index_next_proposer_duty_to_be_served 
                                ==
                                dv.index_next_proposer_duty_to_be_served + 1;
                                
                        assert  inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_helper(                
                                    proposer_duty, 
                                    node, 
                                    dv'.sequence_proposer_duties_to_be_served,
                                    dv'.index_next_proposer_duty_to_be_served
                                );
                        lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_f_serve_proposer_duty( 
                                dvc,
                                proposer_duty,                                
                                dvc',
                                node,
                                dv'.sequence_proposer_duties_to_be_served,    
                                dv'.index_next_proposer_duty_to_be_served 
                            );
                        assert inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty(dv');    
                    
                    case ReceiveRandaoShare(randao_share) =>   
                        lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_f_listen_for_randao_shares(
                                dvc,
                                randao_share,
                                dvc',
                                node,
                                dv'.sequence_proposer_duties_to_be_served,    
                                dv'.index_next_proposer_duty_to_be_served
                            );      
                        assert inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty(dv');       

                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_f_block_consensus_decided(
                                dvc,
                                id,
                                decided_beacon_block,
                                dvc',
                                node,
                                dv'.sequence_proposer_duties_to_be_served,    
                                dv'.index_next_proposer_duty_to_be_served
                            );
                        assert inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty(dv');    

                    case ReceiveSignedBeaconBlock(block_share) =>   
                        lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_f_listen_for_block_signature_shares(
                                dvc,
                                block_share,
                                dvc',
                                node,
                                dv'.sequence_proposer_duties_to_be_served,    
                                dv'.index_next_proposer_duty_to_be_served
                            );      
                        assert inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty(dv');                
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_f_listen_for_new_imported_blocks(
                            dvc,
                            block,
                            dvc',
                            node,
                            dv'.sequence_proposer_duties_to_be_served,    
                            dv'.index_next_proposer_duty_to_be_served
                        );
                        assert inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty(dv');

                    case ResendRandaoRevealSignatureShare =>
                        assert inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty(dv');                       

                    case ResendBlockShare =>  
                        assert inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty(dv');                       
                        
                    case NoEvent => 
                        assert inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty(dv');        
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                assert inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty(dv');        
                
        }   
    }  
    
    lemma lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist(dv)
    ensures inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var process := dv.honest_nodes_states[node];
                var process' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body_f_serve_proposer_duty(process, proposer_duty, process');
                    
                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body_f_listen_for_randao_shares(process, randao_share, process');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(process, id, decided_beacon_block)
                        {
                            lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body_f_block_consensus_decided(process, id, decided_beacon_block, process');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body_f_listen_for_block_signature_shares(process, block_share, process');                        
   
                    case ImportedNewBlock(block) => 
                        var process := f_add_block_to_bn(process, nodeEvent.block);
                        lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body_f_listen_for_new_imported_blocks(process, block, process');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    }

    lemma lem_inv_unchanged_dvc_rs_pubkey_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_unchanged_dvc_rs_pubkey(dv)
    ensures inv_unchanged_dvc_rs_pubkey(dv')
    {   
        assert unchanged_fixed_paras(dv, dv');
        assert dv.honest_nodes_states.Keys == dv'.honest_nodes_states.Keys;

         match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var process := dv.honest_nodes_states[node];
                var process' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_unchanged_dvc_rs_pubkey_body_f_serve_proposer_duty(process, proposer_duty, process');
                    
                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_unchanged_dvc_rs_pubkey_body_f_listen_for_randao_shares(process, randao_share, process');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(process, id, decided_beacon_block)
                        {
                            lem_inv_unchanged_dvc_rs_pubkey_body_f_block_consensus_decided(process, id, decided_beacon_block, process');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_unchanged_dvc_rs_pubkey_body_f_listen_for_block_signature_shares(process, block_share, process');                        
   
                    case ImportedNewBlock(block) => 
                        var process := f_add_block_to_bn(process, nodeEvent.block);
                        lem_inv_unchanged_dvc_rs_pubkey_body_f_listen_for_new_imported_blocks(process, block, process');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    }

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db(dv)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var process := dv.honest_nodes_states[node];
                var process' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_serve_proposer_duty(process, proposer_duty, process');
                    
                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_listen_for_randao_shares(process, randao_share, process');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(process, id, decided_beacon_block)
                        {
                            lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_block_consensus_decided(process, id, decided_beacon_block, process');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_listen_for_block_signature_shares(process, block_share, process');                        
   
                    case ImportedNewBlock(block) => 
                        var process := f_add_block_to_bn(process, nodeEvent.block);
                        lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_listen_for_new_imported_blocks(process, block, process');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    } 

    lemma lem_NextEvent_implies_NextHonestAfterAddingBlockToBn_and_DVC_Spec_Next(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    ensures NextHonestAfterAddingBlockToBn.requires(add_block_to_bn_with_event(s, event.node, event.event), event.node, event.event, event.nodeOutputs, s' )  
    ensures NextHonestAfterAddingBlockToBn(add_block_to_bn_with_event(s, event.node, event.event), event.node, event.event, event.nodeOutputs, s' )  
    ensures DVC_Block_Proposer_Spec_Instr.Next.requires(add_block_to_bn_with_event(s, event.node, event.event).honest_nodes_states[event.node], event.event, s'.honest_nodes_states[event.node], event.nodeOutputs);    
    ensures DVC_Block_Proposer_Spec_Instr.Next(add_block_to_bn_with_event(s, event.node, event.event).honest_nodes_states[event.node], event.event, s'.honest_nodes_states[event.node], event.nodeOutputs);
    { } 

    lemma inv_inv_block_slashing_db_hist_is_monotonic_body(
        process: DVCState,
        nodeEvent: Types.BlockEvent,
        process': DVCState,
        outputs: Outputs        
    )
    requires DVC_Block_Proposer_Spec_Instr.Next.requires(process, nodeEvent, process', outputs)
    requires DVC_Block_Proposer_Spec_Instr.Next(process, nodeEvent, process', outputs)
    ensures inv_block_slashing_db_hist_is_monotonic_body(process, process')
    {
        match nodeEvent
        {
            case ServeProposerDuty(proposer_duty) =>     
                lem_inv_block_slashing_db_hist_is_monotonic_body_f_serve_proposer_duty(process, proposer_duty, process');
                    
            case ReceiveRandaoShare(randao_share) =>       
                lem_inv_block_slashing_db_hist_is_monotonic_body_f_listen_for_randao_shares(process, randao_share, process');    
                
            case BlockConsensusDecided(id, decided_beacon_block) => 
                if f_block_consensus_decided.requires(process, id, decided_beacon_block)
                {
                    lem_inv_block_slashing_db_hist_is_monotonic_body_f_block_consensus_decided(process, id, decided_beacon_block, process');      
                }                 
                
            case ReceiveSignedBeaconBlock(block_share) =>                         
                lem_inv_block_slashing_db_hist_is_monotonic_body_f_listen_for_block_signature_shares(process, block_share, process');                        

            case ImportedNewBlock(block) => 
                var updated_process := f_add_block_to_bn(process, nodeEvent.block);
                lem_inv_block_slashing_db_hist_is_monotonic_body_f_add_block_to_bn(process, block, updated_process);    
                lem_inv_block_slashing_db_hist_is_monotonic_body_f_listen_for_new_imported_blocks(process, block, process');                        
                                        
            case ResendRandaoRevealSignatureShare =>

            case ResendBlockShare =>
                
            case NoEvent => 

        }        
    }
    
    lemma lem_inv_slots_for_sent_validity_predicates_are_stored_in_block_slashing_db_hist_helper(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        cid: Slot,
        hn: BLSPubkey,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires inv_only_dv_construct_complete_signing_functions(s)    
    requires hn in s.honest_nodes_states.Keys
    requires inv_slots_for_sent_validity_predicates_are_stored_in_block_slashing_db_hist_body(s, hn, s.honest_nodes_states[hn], cid)
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist(s)
    ensures inv_slots_for_sent_validity_predicates_are_stored_in_block_slashing_db_hist_body(s', hn, s'.honest_nodes_states[hn], cid)
    {
        assert s.block_share_network.allMessagesSent <= s'.block_share_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>

                var s_w_honest_node_states_updated := f_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_get_s_w_honest_node_states_updated(s, node, nodeEvent);           

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

                assert
                    Block_Consensus_Spec.Next(
                        s_consensus,
                        validityPredicates,
                        s'_consensus,
                        output
                    );
                   
                if  hn in s'.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions.Keys  
                {
                    if hn in  s.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions.Keys
                    {
                        assert inv_slots_for_sent_validity_predicates_are_stored_in_block_slashing_db_hist_body(s, hn, s.honest_nodes_states[hn], cid);

                        assert cid in s.honest_nodes_states[hn].block_consensus_engine_state.block_slashing_db_hist.Keys;
                    }
                    else 
                    {
                        assert hn in validityPredicates;
                        assert cid in s.honest_nodes_states[hn].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys;
                        assert inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(s.honest_nodes_states[hn]);
                        assert cid in s.honest_nodes_states[hn].block_consensus_engine_state.block_slashing_db_hist.Keys;
                    }

                    if hn == node 
                    {
                        lem_NextEvent_implies_NextHonestAfterAddingBlockToBn_and_DVC_Spec_Next(s, event, s');
                        assert DVC_Block_Proposer_Spec_Instr.Next.requires(s_w_honest_node_states_updated.honest_nodes_states[hn], nodeEvent, s'.honest_nodes_states[hn], nodeOutputs);
                        assert DVC_Block_Proposer_Spec_Instr.Next(s_w_honest_node_states_updated.honest_nodes_states[hn], nodeEvent, s'.honest_nodes_states[hn], nodeOutputs);
                        inv_inv_block_slashing_db_hist_is_monotonic_body(s_w_honest_node_states_updated.honest_nodes_states[hn], nodeEvent, s'.honest_nodes_states[hn], nodeOutputs);
                        assert s_w_honest_node_states_updated.honest_nodes_states[hn].block_consensus_engine_state.block_slashing_db_hist.Keys <= s'.honest_nodes_states[hn].block_consensus_engine_state.block_slashing_db_hist.Keys;
                        assert cid in s'.honest_nodes_states[hn].block_consensus_engine_state.block_slashing_db_hist.Keys;
                    }
                    else 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        assert cid in s'.honest_nodes_states[hn].block_consensus_engine_state.block_slashing_db_hist.Keys;
                    }
                }  

                         
            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) => 
                assert s'.consensus_instances_on_beacon_block == s.consensus_instances_on_beacon_block;
                assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                 
                if
                    && hn in s'.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions.Keys
                {
                    assert inv_slots_for_sent_validity_predicates_are_stored_in_block_slashing_db_hist_body(s, hn, s.honest_nodes_states[hn], cid);
                    assert cid in s.honest_nodes_states[hn].block_consensus_engine_state.block_slashing_db_hist.Keys;
                    assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                    assert cid in s'.honest_nodes_states[hn].block_consensus_engine_state.block_slashing_db_hist.Keys;                    
                } 

        }
    }   

    lemma lem_inv_slots_for_sent_validity_predicates_are_stored_in_block_slashing_db_hist(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_all_honest_nodes_is_a_quorum(s)
    requires inv_the_same_node_status_in_dv_and_ci(s)
    requires inv_only_dv_construct_complete_signing_functions(s)    
    requires inv_slots_for_sent_validity_predicates_are_stored_in_block_slashing_db_hist(s)   
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist(s)
    ensures inv_slots_for_sent_validity_predicates_are_stored_in_block_slashing_db_hist(s')   
    {
        forall hn: BLSPubkey, slot: Slot |
            hn in s'.honest_nodes_states.Keys
        ensures inv_slots_for_sent_validity_predicates_are_stored_in_block_slashing_db_hist_body(s', hn, s'.honest_nodes_states[hn], slot)    
        {
            lem_inv_slots_for_sent_validity_predicates_are_stored_in_block_slashing_db_hist_helper(s, event, slot, hn, s');
        }
    } 

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties(dv)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties(dv')
    {  

        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>    
                        lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_serve_proposer_duty(
                            dvc,
                            proposer_duty,
                            dvc'
                        );
                        assert inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties(dv'); 
                        
                    case ReceiveRandaoShare(randao_share) =>
                        lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_listen_for_randao_shares(dvc, randao_share, dvc');    
                        assert inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties(dv'); 

                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');      
                        }      
                        assert inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties(dv');         

                    case ReceiveSignedBeaconBlock(block_share) =>   
                        lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_listen_for_block_signature_shares(dvc, block_share, dvc');                        
                        assert inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties(dv');              
   
                    case ImportedNewBlock(block) =>
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_listen_for_new_imported_blocks(dvc, block, dvc');                         
                        assert inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties(dv');     

                    case ResendRandaoRevealSignatureShare =>
                        lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_resend_randao_share(dvc, dvc');
                        assert inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties(dv');     
                                          
                    case ResendBlockShare =>  
                        lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_resend_block_share(dvc, dvc');
                        assert inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties(dv');     

                    case NoEvent => 
                        assert dvc == dvc'; 
                        assert  && dvc.all_rcvd_duties == dvc'.all_rcvd_duties
                                && dvc.latest_proposer_duty == dvc'.latest_proposer_duty
                                ;  
                        assert inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties(dv'); 
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                assert inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties(dv');        
        }   
    }

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty(dv)
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties(dv)
    requires inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_proposer_duties(dv)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty(dv')
    {  
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>    
                        assert inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_proposer_duties_body(dvc, proposer_duty);
                        lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_serve_proposer_duty(
                            dvc,
                            proposer_duty,
                            dvc'
                        );
                        assert inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty(dv');         

                    case ReceiveRandaoShare(randao_share) => 
                        lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_listen_for_randao_shares(dvc, randao_share, dvc');    
                        assert inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty(dv');         

                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');      
                        } 
                        assert inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty(dv');         

                    case ReceiveSignedBeaconBlock(block_share) =>   
                        lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_listen_for_block_signature_shares(dvc, block_share, dvc');                        
                        assert inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty(dv');              
   
                    case ImportedNewBlock(block) => 
                        var new_dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_add_block_to_bn(dvc, block, new_dvc);                        
                        lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_listen_for_new_imported_blocks(new_dvc, block, dvc');                        
                        assert inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty(dv');     

                    case ResendRandaoRevealSignatureShare =>
                        lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_resend_randao_share(dvc, dvc');
                                          
                    case ResendBlockShare =>  
                        lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_resend_block_share(dvc, dvc');
                        assert inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty(dv');     

                    case NoEvent => 
                        assert dvc == dvc'; 
                        assert dvc.all_rcvd_duties == dvc'.all_rcvd_duties;  
                        assert inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty(dv'); 
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                assert inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty(dv');        
                
        }   
    }

    lemma lem_validNodeEvent_ServeProposerDuty(
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
    requires nodeEvent.ServeProposerDuty?
    ensures node in dv.honest_nodes_states.Keys
    ensures validNodeEvent(dv, node, nodeEvent)
    { 
        assert  NextEventPreCond(dv, event);
        assert  NextHonestNodePrecond(
                    add_block_to_bn_with_event(
                        dv, 
                        event.node, 
                        event.event).honest_nodes_states[event.node], 
                    event.event
                );   
        assert  validNodeEvent(dv, node, nodeEvent);   
    }

    lemma lem_inv_unique_rcvd_proposer_duty_per_slot_ServeProposerDuty(
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

    requires inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty(dv)
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty(dv)
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties(dv)

    requires inv_unique_rcvd_proposer_duty_per_slot(dv)
    ensures inv_unique_rcvd_proposer_duty_per_slot(dv')
    { 
        lem_validNodeEvent_ServeProposerDuty(
            dv,
            event,
            dv',
            node,
            nodeEvent,
            nodeOutputs
        );
        assert  validNodeEvent(dv, node, nodeEvent);
        assert  node in dv.honest_nodes_states.Keys;

        var dv_duty_queue := dv.sequence_proposer_duties_to_be_served;
        var dv_index := dv.index_next_proposer_duty_to_be_served;
        var next_duty_and_node := dv_duty_queue[dv_index];
        var dvc := dv.honest_nodes_states[node];
        var dvc' := dv'.honest_nodes_states[node];

        assert  && proposer_duty == next_duty_and_node.proposer_duty
                && node == next_duty_and_node.node
                ;        
        
        assert  dvc.all_rcvd_duties + {proposer_duty} == dvc'.all_rcvd_duties;


        forall d1: ProposerDuty, d2: ProposerDuty | 
            && d1 in dvc'.all_rcvd_duties
            && d2 in dvc'.all_rcvd_duties
            && d1.slot == d2.slot
        ensures d1 == d2
        {
            if d1 != d2
            {
                if d1 in dvc.all_rcvd_duties && d2 in dvc.all_rcvd_duties
                {
                    assert  d1.slot == d2.slot;                    
                }
                else
                {
                    if d1 !in dvc.all_rcvd_duties 
                    {
                        assert  && d1 == proposer_duty
                                && d2 in dvc.all_rcvd_duties
                                ;
                        assert  dvc.latest_proposer_duty.isPresent();
                        calc 
                        {
                            d1.slot;
                            <=
                            dvc.latest_proposer_duty.safe_get().slot;
                            <
                            proposer_duty.slot;
                        }
                    }
                    else
                    {
                        assert  && d2 == proposer_duty
                                && d1 in dvc.all_rcvd_duties
                                ;
                        assert  dvc.latest_proposer_duty.isPresent();
                        calc 
                        {
                            d2.slot;
                            <=
                            dvc.latest_proposer_duty.safe_get().slot;
                            <
                            proposer_duty.slot;
                        }
                    }
                }
            }
        }
    }

    lemma lem_inv_unique_rcvd_proposer_duty_per_slot_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_unique_rcvd_proposer_duty_per_slot(dv)
    requires inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty(dv)
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty(dv)
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties(dv)
    ensures inv_unique_rcvd_proposer_duty_per_slot(dv')
    {  
        match event 
        {

            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];

                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>   
                        lem_inv_unique_rcvd_proposer_duty_per_slot_ServeProposerDuty(
                            dv,
                            event,
                            dv',
                            node,
                            nodeEvent,
                            nodeOutputs,
                            proposer_duty
                        );  
                        assert inv_unique_rcvd_proposer_duty_per_slot_body(dvc');         
                        assert inv_unique_rcvd_proposer_duty_per_slot(dv');  

                    case ReceiveRandaoShare(randao_share) =>
                        assert inv_unique_rcvd_proposer_duty_per_slot(dv');         

                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        assert inv_unique_rcvd_proposer_duty_per_slot(dv');         

                    case ReceiveSignedBeaconBlock(block_share) =>   
                        assert inv_unique_rcvd_proposer_duty_per_slot(dv');              
   
                    case ImportedNewBlock(block) => 
                        assert inv_unique_rcvd_proposer_duty_per_slot(dv');   

                    case ResendRandaoRevealSignatureShare =>  
                        assert inv_unique_rcvd_proposer_duty_per_slot(dv');     
                                          
                    case ResendBlockShare =>  
                        assert inv_unique_rcvd_proposer_duty_per_slot(dv');     

                    case NoEvent => 
                        assert dvc == dvc'; 
                        assert dvc.all_rcvd_duties == dvc'.all_rcvd_duties;  
                        assert inv_unique_rcvd_proposer_duty_per_slot(dv'); 
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                assert inv_unique_rcvd_proposer_duty_per_slot(dv');        
        }   
    }

    predicate lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_new_precond(s: DVState) 
    {
        && inv_all_honest_nodes_is_a_quorum(s)
        && inv_nodes_in_consensus_instances_are_in_dv(s)
        && inv_only_dv_construct_complete_signing_functions(s)
        && inv_the_same_node_status_in_dv_and_ci(s)    
        && inv_in_transit_messages_are_in_allMessagesSent(s)
        && inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums(s) 
        && inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(s) 
        && inv_blocks_of_in_transit_block_shares_are_decided_values(s) 
        && inv_seq_of_proposer_duties_is_ordered(s) 
        && inv_available_current_proposer_duty_is_latest_proposer_duty(s)
        && inv_only_dv_construct_complete_signing_functions(s)
        && inv_rcvd_block_shares_are_in_all_sent_messages(s) 
        && inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s)
        && inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(s)      
        && inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)    
        && inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(s)    
        && inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(s)         
    }

    lemma lem_inv_consensus_instance_isConditionForSafetyTrue_dv_next(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )    
    requires NextEvent.requires(dv, event, dv')  
    requires NextEvent(dv, event, dv')  
    requires inv_consensus_instance_isConditionForSafetyTrue(dv)
    ensures inv_consensus_instance_isConditionForSafetyTrue(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];   
                
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>                           

                    case ReceiveRandaoShare(randao_share) =>                         
                        
                    case BlockConsensusDecided(id, decided_proposer_data) => 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                       
                    case ImportedNewBlock(block) => 
                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>                                                                     

                    case NoEvent => 
                        
                }
                
            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    }  

    lemma lem_inv_unchanged_decision_dv(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState,
        slot: Slot
    )
    requires NextEventPreCond(s, event) 
    requires NextEvent(s, event, s')   
    requires inv_consensus_instance_isConditionForSafetyTrue(s)
    requires && slot in s.consensus_instances_on_beacon_block.Keys 
             && s.consensus_instances_on_beacon_block[slot].decided_value.isPresent()
    ensures  && s'.consensus_instances_on_beacon_block[slot].decided_value.isPresent()
             && s.consensus_instances_on_beacon_block[slot].decided_value.safe_get()
                == 
                s'.consensus_instances_on_beacon_block[slot].decided_value.safe_get()
    { }

    lemma lem_inv_decisions_of_consensus_instances_are_unchanged(
        dv: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        dv': DVState
    )
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')     
    requires inv_consensus_instance_isConditionForSafetyTrue(dv)
    ensures ( forall slot: Slot | slot in dv.consensus_instances_on_beacon_block.Keys ::
                    dv.consensus_instances_on_beacon_block[slot].decided_value.isPresent()
                    ==>
                    ( && dv'.consensus_instances_on_beacon_block[slot].decided_value.isPresent()
                      && dv.consensus_instances_on_beacon_block[slot].decided_value.safe_get()  
                         ==
                         dv'.consensus_instances_on_beacon_block[slot].decided_value.safe_get()
                    )
            )
    { }

          

    lemma lem_unique_owner_of_block_share(
        rs_pubkey: BLSPubkey,
        rs_pubkey': BLSPubkey,
        block_share: SignedBeaconBlock
    )
    requires pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
    requires pred_is_the_owner_of_a_block_share(rs_pubkey', block_share)
    ensures rs_pubkey == rs_pubkey'
    {
        var decided_beacon_block := block_share.block;
        var block_signing_root := compute_block_signing_root(decided_beacon_block);
        assert verify_bls_signature(block_signing_root, block_share.signature, rs_pubkey);
        assert verify_bls_signature(block_signing_root, block_share.signature, rs_pubkey');
        rs_block_sign_and_verification_propeties();
        assert rs_pubkey == rs_pubkey';
    }

    
}