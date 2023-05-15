include "invs_fnc_1.dfy"

include "../../../../common/commons.dfy"

include "../../common/dvc_block_proposer_instrumented.dfy"
include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_block_proposer.dfy"
include "../inv.dfy"

include "../../common/common_proofs.dfy"
include "../../../bn_axioms.dfy"
include "../../../rs_axioms.dfy"
include "../inv.dfy"

module Invs_DV_Next_1
{
    import opened Types 
    
    import opened Common_Functions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Block_Proposer_Spec_Instr
    import opened Consensus_Engine_Instr
    import opened Block_Inv_With_Empty_Initial_Block_Slashing_DB
    import opened DV_Block_Proposer_Spec
    import opened Fnc_Invs_1
    import opened Set_Seq_Helper
    import opened Signing_Methods

    lemma lem_inv_all_honest_nodes_is_a_quorum_dv_next(dv: Block_DVState, event: DVBlockEvent, dv': Block_DVState)       
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_all_honest_nodes_is_a_quorum(dv)
    ensures inv_all_honest_nodes_is_a_quorum(dv')
    { }    

    lemma lem_inv_nodes_in_consensus_instances_are_in_dv_dv_next(dv: Block_DVState, event: DVBlockEvent, dv': Block_DVState)       
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_nodes_in_consensus_instances_are_in_dv(dv)
    ensures inv_nodes_in_consensus_instances_are_in_dv(dv')
    { }    

    lemma lem_inv_only_dv_construct_complete_signing_functions_dv_next(dv: Block_DVState, event: DVBlockEvent, dv': Block_DVState)       
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_only_dv_construct_complete_signing_functions(dv)
    ensures inv_only_dv_construct_complete_signing_functions(dv')
    { }    

    lemma lem_inv_current_proposer_duty_is_a_rcvd_duty_dv_next(
        dv: Block_DVState,
        event: DVBlockEvent,
        dv': Block_DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_current_proposer_duty_is_a_rcvd_duty(dv)
    ensures inv_current_proposer_duty_is_a_rcvd_duty(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_current_proposer_duty_is_a_rcvd_duty_body_f_serve_proposer_duty(dvc, proposer_duty, dvc');
                    
                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_current_proposer_duty_is_a_rcvd_duty_body_f_listen_for_randao_shares(dvc, randao_share, dvc');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            lem_inv_current_proposer_duty_is_a_rcvd_duty_body_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_current_proposer_duty_is_a_rcvd_duty_body_f_listen_for_block_signature_shares(dvc, block_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_current_proposer_duty_is_a_rcvd_duty_body_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    }     

    lemma lem_inv_latest_served_duty_is_a_rcvd_duty_dv_next(
        dv: Block_DVState,
        event: DVBlockEvent,
        dv': Block_DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_latest_served_duty_is_a_rcvd_duty(dv)
    ensures inv_latest_served_duty_is_a_rcvd_duty(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_latest_served_duty_is_a_rcvd_duty_body_f_serve_proposer_duty(dvc, proposer_duty, dvc');
                    
                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_latest_served_duty_is_a_rcvd_duty_body_f_listen_for_randao_shares(dvc, randao_share, dvc');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            lem_inv_latest_served_duty_is_a_rcvd_duty_body_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_latest_served_duty_is_a_rcvd_duty_body_f_listen_for_block_signature_shares(dvc, block_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_latest_served_duty_is_a_rcvd_duty_body_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    } 

    lemma lem_inv_none_latest_proposer_duty_implies_none_current_proposer_duty_dv_next(
        dv: Block_DVState,
        event: DVBlockEvent,
        dv': Block_DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_none_latest_proposer_duty_implies_none_current_proposer_duty(dv)
    ensures inv_none_latest_proposer_duty_implies_none_current_proposer_duty(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body_f_serve_proposer_duty(dvc, proposer_duty, dvc');
                    
                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body_f_listen_for_randao_shares(dvc, randao_share, dvc');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            lem_inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body_f_listen_for_block_signature_shares(dvc, block_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    } 

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_dv_next(
        dv: Block_DVState,
        event: DVBlockEvent,
        dv': Block_DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_current_proposer_duty_is_either_none_or_latest_proposer_duty(dv)
    ensures inv_current_proposer_duty_is_either_none_or_latest_proposer_duty(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body_f_serve_proposer_duty(dvc, proposer_duty, dvc');
                    
                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body_f_listen_for_randao_shares(dvc, randao_share, dvc');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            lem_inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body_f_listen_for_block_signature_shares(dvc, block_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    } 

    lemma lem_inv_available_current_proposer_duty_is_latest_proposer_duty_dv_next(
        dv: Block_DVState,
        event: DVBlockEvent,
        dv': Block_DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_available_current_proposer_duty_is_latest_proposer_duty(dv)
    ensures inv_available_current_proposer_duty_is_latest_proposer_duty(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_available_current_proposer_duty_is_latest_proposer_duty_body_f_serve_proposer_duty(dvc, proposer_duty, dvc');
                    
                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_available_current_proposer_duty_is_latest_proposer_duty_body_f_listen_for_randao_shares(dvc, randao_share, dvc');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            lem_inv_available_current_proposer_duty_is_latest_proposer_duty_body_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_available_current_proposer_duty_is_latest_proposer_duty_body_f_listen_for_block_signature_shares(dvc, block_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_available_current_proposer_duty_is_latest_proposer_duty_body_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    } 

    lemma lem_inv_seq_of_proposer_duties_is_ordered_dv_next(
        dv: Block_DVState,
        event: DVBlockEvent,
        dv': Block_DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')      
    requires inv_seq_of_proposer_duties_is_ordered(dv)
    ensures inv_seq_of_proposer_duties_is_ordered(dv')
    { 
        assert dv.sequence_proposer_duties_to_be_served == dv'.sequence_proposer_duties_to_be_served;
    }

    lemma lem_inv_no_duplicated_proposer_duties_dv_next(
        dv: Block_DVState,
        event: DVBlockEvent,
        dv': Block_DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')      
    requires inv_no_duplicated_proposer_duties(dv')    
    ensures inv_no_duplicated_proposer_duties(dv')    
    { }

    lemma lem_inv_unchanged_dv_seq_of_proposer_duties_dv_next(
        dv: Block_DVState,
        event: DVBlockEvent,
        dv': Block_DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')      
    ensures inv_unchanged_dv_seq_of_proposer_duties(dv, dv')
    { }

    

    lemma lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_dv_next(
        dv: Block_DVState,
        event: DVBlockEvent,
        dv': Block_DVState
    )    
    requires NextEvent.requires(dv, event, dv')  
    requires NextEvent(dv, event, dv')  
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv)
    ensures inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv')
    {        
        assert dv.sequence_proposer_duties_to_be_served == dv'.sequence_proposer_duties_to_be_served;

        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];   
                var sequence_proposer_duties_to_be_served := dv.sequence_proposer_duties_to_be_served;
                var index_next_proposer_duty_to_be_served := dv.index_next_proposer_duty_to_be_served;
                
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        assert index_next_proposer_duty_to_be_served + 1 == dv'.index_next_proposer_duty_to_be_served;
                        assert pred_proposer_duty_is_from_dv_seq_of_proposer_duties_body(  
                            proposer_duty,
                            node,
                            sequence_proposer_duties_to_be_served, 
                            index_next_proposer_duty_to_be_served + 1
                        );
                        assert inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                                        node, 
                                        dvc, 
                                        sequence_proposer_duties_to_be_served, 
                                        index_next_proposer_duty_to_be_served + 1
                                );
                        lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_serve_proposer_duty(
                            dvc,
                            proposer_duty,
                            dvc',
                            node,
                            sequence_proposer_duties_to_be_served,
                            index_next_proposer_duty_to_be_served + 1
                        );
                        assert inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                                        node, 
                                        dvc', 
                                        sequence_proposer_duties_to_be_served, 
                                        index_next_proposer_duty_to_be_served + 1
                                );
                        assert inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv');
                    
                    case ReceiveRandaoShare(randao_share) =>                         
                        assert inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                                        node, 
                                        dvc, 
                                        sequence_proposer_duties_to_be_served, 
                                        index_next_proposer_duty_to_be_served
                                );
                        lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_listen_for_randao_shares(
                            dvc,
                            randao_share,
                            dvc',
                            node,
                            sequence_proposer_duties_to_be_served,
                            index_next_proposer_duty_to_be_served
                        );
                        assert inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv');

                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_block_consensus_decided(
                            dvc,
                            id,
                            decided_beacon_block, 
                            dvc',
                            node,
                            sequence_proposer_duties_to_be_served,
                            index_next_proposer_duty_to_be_served
                        );
                        
                    case ReceiveSignedBeaconBlock(block_share) =>      
                        lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_listen_for_block_signature_shares(
                            dvc,
                            block_share,
                            dvc',
                            node,
                            sequence_proposer_duties_to_be_served,
                            index_next_proposer_duty_to_be_served
                        );       
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_listen_for_new_imported_blocks(
                            dvc,
                            block,
                            dvc',
                            node,
                            sequence_proposer_duties_to_be_served,
                            index_next_proposer_duty_to_be_served
                        );
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>

                    case NoEvent => 

                }
                
            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    }     

    lemma lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_dv_next(
        dv: Block_DVState,
        event: DVBlockEvent,
        dv': Block_DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_available_current_proposer_duty_is_latest_proposer_duty(dv)
    requires inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none(dv)
    ensures inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_serve_proposer_duty(dvc, proposer_duty, dvc');
                    
                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_listen_for_randao_shares(dvc, randao_share, dvc');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_listen_for_block_signature_shares(dvc, block_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    } 

    lemma lem_inv_every_proposer_duty_before_dv_index_next_proposer_duty_to_be_served_was_delivered_f_serve_proposer_duty(
        dv: Block_DVState,
        event: DVBlockEvent,
        node: BLSPubkey,
        nodeEvent: Types.BlockEvent,
        nodeOutputs: BlockOutputs,
        dv': Block_DVState
    )  
    requires inv_all_honest_nodes_is_a_quorum(dv)    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.HonestNodeTakingStep?
    requires NextHonestAfterAddingBlockToBn.requires(dv, node, nodeEvent, nodeOutputs, dv');
    requires NextHonestAfterAddingBlockToBn(dv, node, nodeEvent, nodeOutputs, dv');      
    requires nodeEvent.ServeProposerDuty?
    requires inv_unchanged_dv_seq_of_proposer_duties(dv, dv')
    requires inv_every_proposer_duty_before_dv_index_next_proposer_duty_to_be_served_was_delivered(dv)
    ensures inv_every_proposer_duty_before_dv_index_next_proposer_duty_to_be_served_was_delivered(dv')
    {
        var dvc := dv.honest_nodes_states[node];
        var dvc' := dv'.honest_nodes_states[node];

        match nodeEvent
        {
            case ServeProposerDuty(proposer_duty) =>     
                var index := dv.index_next_proposer_duty_to_be_served;
                var new_duty := dv.sequence_proposer_duties_to_be_served[index].proposer_duty;                                
                lem_updated_all_rcvd_duties_f_serve_proposer_duty(dvc, new_duty, dvc');   
                assert dvc'.all_rcvd_duties == dvc.all_rcvd_duties + {new_duty};                                                                                                       
                var new_index := dv'.index_next_proposer_duty_to_be_served;
                assert index + 1 == new_index;
                
                forall k: nat | ( && 0 <= k < new_index
                                    && dv'.sequence_proposer_duties_to_be_served[k].node in dv'.honest_nodes_states.Keys
                                )    
                ensures index + 1 == new_index
                ensures dv'.sequence_proposer_duties_to_be_served[k].proposer_duty
                            in dv'.honest_nodes_states[dv'.sequence_proposer_duties_to_be_served[k].node].all_rcvd_duties                            
                {
                    var duty_and_node: ProposerDutyAndNode := dv.sequence_proposer_duties_to_be_served[k];
                    var duty := duty_and_node.proposer_duty;
                    var hn := duty_and_node.node;
                    var dvc_state := dv.honest_nodes_states[hn];
                    var dvc_state' := dv'.honest_nodes_states[hn];

                    if hn == node
                    {
                        if k < index
                        {     
                            assert inv_every_proposer_duty_before_dv_index_next_proposer_duty_to_be_served_was_delivered_body(dvc_state, duty);
                            assert inv_every_proposer_duty_before_dv_index_next_proposer_duty_to_be_served_was_delivered_body(dvc_state', duty);
                        }
                        else
                        {
                            assert k == index;
                            assert k == new_index - 1;
                            lem_updated_all_rcvd_duties_f_serve_proposer_duty(dvc, new_duty, dvc');                                  
                            assert dvc'.all_rcvd_duties == dvc.all_rcvd_duties + {proposer_duty};
                            assert proposer_duty in dvc'.all_rcvd_duties;                                
                            assert inv_every_proposer_duty_before_dv_index_next_proposer_duty_to_be_served_was_delivered_body(dvc_state', duty);
                        }
                    }
                    else
                    {
                        assert dvc_state == dvc_state';
                        assert inv_every_proposer_duty_before_dv_index_next_proposer_duty_to_be_served_was_delivered_body(dvc_state', duty);
                    }
                    
                    assert inv_every_proposer_duty_before_dv_index_next_proposer_duty_to_be_served_was_delivered_body(dvc_state', duty);
                }
                
                assert inv_every_proposer_duty_before_dv_index_next_proposer_duty_to_be_served_was_delivered(dv');                
        }
    }

    lemma lem_inv_every_proposer_duty_before_dv_index_next_proposer_duty_to_be_served_was_delivered_dv_next(
        dv: Block_DVState,
        event: DVBlockEvent,
        dv': Block_DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_all_honest_nodes_is_a_quorum(dv) 
    requires inv_unchanged_dv_seq_of_proposer_duties(dv, dv')
    requires inv_every_proposer_duty_before_dv_index_next_proposer_duty_to_be_served_was_delivered(dv)
    ensures inv_every_proposer_duty_before_dv_index_next_proposer_duty_to_be_served_was_delivered(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_every_proposer_duty_before_dv_index_next_proposer_duty_to_be_served_was_delivered_f_serve_proposer_duty(
                            dv,
                            event,
                            node,
                            nodeEvent,
                            nodeOutputs,
                            dv'
                        );
                    
                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_updated_all_rcvd_duties_f_listen_for_randao_shares(dvc, randao_share, dvc');  
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            lem_updated_all_rcvd_duties_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');    
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_updated_all_rcvd_duties_f_listen_for_block_signature_shares(dvc, block_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_updated_all_rcvd_duties_f_listen_for_new_imported_blocks(dvc, block, dvc');
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    }

    lemma lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_dv_next(
        dv: Block_DVState,
        event: DVBlockEvent,
        dv': Block_DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_current_proposer_duty_is_a_rcvd_duty(dv)
    requires inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties(dv)
    ensures inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body_f_serve_proposer_duty(dvc, proposer_duty, dvc');
                    
                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body_f_listen_for_randao_shares(dvc, randao_share, dvc');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body_f_listen_for_block_signature_shares(dvc, block_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    } 
    
    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_dv_next(
        dv: Block_DVState,
        event: DVBlockEvent,
        dv': Block_DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_current_proposer_duty_is_a_rcvd_duty(dv)
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k(dv)
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeProposerDuty(proposer_duty) =>     
                        lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_serve_proposer_duty(dvc, proposer_duty, dvc');
                    
                    case ReceiveRandaoShare(randao_share) =>                         
                        lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_listen_for_randao_shares(dvc, randao_share, dvc');    
                        
                    case BlockConsensusDecided(id, decided_beacon_block) => 
                        if f_block_consensus_decided.requires(dvc, id, decided_beacon_block)
                        {
                            lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_block_consensus_decided(dvc, id, decided_beacon_block, dvc');      
                        }                 
                        
                    case ReceiveSignedBeaconBlock(block_share) =>                         
                        lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_listen_for_block_signature_shares(dvc, block_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendRandaoRevealSignatureShare =>

                    case ResendBlockShare =>
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
        }   
    } 

}