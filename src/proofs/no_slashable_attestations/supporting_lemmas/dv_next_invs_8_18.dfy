include "../../../common/commons.dfy"
include "../common/attestation_creation_instrumented.dfy"
include "../../../specs/consensus/consensus.dfy"
include "../../../specs/network/network.dfy"
include "../../../specs/dv/dv_attestation_creation.dfy"
include "inv.dfy"
include "fnc_invs_1_26.dfy"
include "../../common/helper_sets_lemmas.dfy"
include "proofs_intermediate_steps.dfy"
include "dv_next_invs_1_7.dfy"

module DV_Next_Invs_8_18
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Fnc_Invs_1_26
    import opened Helper_Sets_Lemmas
    import opened Proofs_Intermediate_Steps
    import opened DV_Next_Invs_1_7

     

    lemma lemma_inv_none_latest_served_duty_implies_none_current_att_duty_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')      
    requires inv_none_latest_served_duty_implies_none_current_att_duty(dv)
    ensures inv_none_latest_served_duty_implies_none_current_att_duty(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                assert inv_none_latest_served_duty_implies_none_current_att_duty_body(dvc);
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                             
                        lemma_inv_none_latest_served_duty_implies_none_current_att_duty_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv_none_latest_served_duty_implies_none_current_att_duty_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lemma_inv_none_latest_served_duty_implies_none_current_att_duty_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, nodeEvent.block);
                        lemma_inv_none_latest_served_duty_implies_none_current_att_duty_add_block_to_bn(dvc, nodeEvent.block, dvc_mod);
                        assert inv_none_latest_served_duty_implies_none_current_att_duty_body(dvc_mod);
                        lemma_inv_none_latest_served_duty_implies_none_current_att_duty_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_none_latest_served_duty_implies_none_current_att_duty_body(dvc');
                        
                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }  

    lemma lemma_inv_current_att_duty_is_either_none_or_latest_served_duty_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')      
    requires inv_current_att_duty_is_either_none_or_latest_served_duty(dv)
    ensures inv_current_att_duty_is_either_none_or_latest_served_duty(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                assert inv_current_att_duty_is_either_none_or_latest_served_duty_body(dvc);
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                             
                        lemma_inv_current_att_duty_is_either_none_or_latest_served_duty_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv_current_att_duty_is_either_none_or_latest_served_duty_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lemma_inv_current_att_duty_is_either_none_or_latest_served_duty_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, nodeEvent.block);
                        lemma_inv_current_att_duty_is_either_none_or_latest_served_duty_add_block_to_bn(dvc, nodeEvent.block, dvc_mod);
                        assert inv_current_att_duty_is_either_none_or_latest_served_duty_body(dvc_mod);
                        lemma_inv_current_att_duty_is_either_none_or_latest_served_duty_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_current_att_duty_is_either_none_or_latest_served_duty_body(dvc');
                        
                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }  

    lemma lemma_inv_not_none_current_att_duty_is_latest_served_att_duty_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')          
    requires inv_not_none_current_att_duty_is_latest_served_att_duty(dv)
    ensures inv_not_none_current_att_duty_is_latest_served_att_duty(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                assert inv_not_none_current_att_duty_is_latest_served_att_duty_body(dvc);
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                             
                        lemma_inv_not_none_current_att_duty_is_latest_served_att_duty_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv_not_none_current_att_duty_is_latest_served_att_duty_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lemma_inv_not_none_current_att_duty_is_latest_served_att_duty_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, nodeEvent.block);
                        lemma_inv_not_none_current_att_duty_is_latest_served_att_duty_add_block_to_bn(dvc, nodeEvent.block, dvc_mod);
                        assert inv_not_none_current_att_duty_is_latest_served_att_duty_body(dvc_mod);
                        lemma_inv_not_none_current_att_duty_is_latest_served_att_duty_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_not_none_current_att_duty_is_latest_served_att_duty_body(dvc');
                        
                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }  

    
    lemma lemma_inv_is_sequence_attestation_duties_to_be_serves_orders_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')      
    requires inv_is_sequence_attestation_duties_to_be_serves_orders(dv)
    ensures inv_is_sequence_attestation_duties_to_be_serves_orders(dv')
    { 
        assert dv.sequence_attestation_duties_to_be_served == dv'.sequence_attestation_duties_to_be_served;
    }
    

    // It takes more than 60 seconds to prove lemma_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_dv_next.
    lemma lemma_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')      
    requires inv_none_latest_served_duty_implies_none_current_att_duty(dv)
    requires inv_no_queued_att_duty_if_latest_served_att_duty_is_none(dv)
    ensures inv_no_queued_att_duty_if_latest_served_att_duty_is_none(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                assert inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(dvc);
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                             
                        lemma_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lemma_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, nodeEvent.block);
                        lemma_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_add_block_to_bn(dvc, nodeEvent.block, dvc_mod);
                        assert inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(dvc_mod);
                        lemma_inv_no_queued_att_duty_if_latest_served_att_duty_is_none_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_no_queued_att_duty_if_latest_served_att_duty_is_none_body(dvc');
                        
                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }  

    lemma lemma_inv_strictly_increasing_queue_of_att_duties_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_quorum_constraints(dv)  
    requires inv_unchanged_honesty(dv)
    requires inv4(dv)
    requires inv5(dv)
    requires inv_is_sequence_attestation_duties_to_be_serves_orders(dv)
    requires concl_future_att_duty_is_higher_than_queued_att_duty(dv)
    requires inv_strictly_increasing_queue_of_att_duties(dv)
    ensures inv_strictly_increasing_queue_of_att_duties(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                                                                     
                        lemma_inv_strictly_increasing_queue_of_att_duties_f_serve_attestation_duty(dvc, attestation_duty, dvc');                                                
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv_strictly_increasing_queue_of_att_duties_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lemma_inv_strictly_increasing_queue_of_att_duties_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lemma_inv_strictly_increasing_queue_of_att_duties_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_strictly_increasing_queue_of_att_duties_body(dvc_mod);
                        lemma_inv_strictly_increasing_queue_of_att_duties_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_strictly_increasing_queue_of_att_duties_body(dvc');
                    
                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                assert inv_strictly_increasing_queue_of_att_duties_body(dvc');
                forall n | n in dv'.honest_nodes_states.Keys 
                ensures inv_strictly_increasing_queue_of_att_duties_body(dv'.honest_nodes_states[n]);
                {
                    if n != node 
                    {
                        assert dv.honest_nodes_states[n] == dv'.honest_nodes_states[n];
                        assert inv_strictly_increasing_queue_of_att_duties_body(dv'.honest_nodes_states[n]);
                    }
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                assert inv_strictly_increasing_queue_of_att_duties(dv');
                
        }   
    }  

    lemma lemma_inv_queued_att_duty_is_higher_than_latest_served_att_duty_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_quorum_constraints(dv)  
    requires inv_unchanged_honesty(dv)  
    requires inv4(dv)
    requires inv5(dv)
    requires inv_latest_served_duty_is_rcvd_duty(dv)
    requires inv_is_sequence_attestation_duties_to_be_serves_orders(dv)  
    requires inv_strictly_increasing_queue_of_att_duties(dv)
    requires inv_queued_att_duty_is_higher_than_latest_served_att_duty(dv)
    ensures inv_queued_att_duty_is_higher_than_latest_served_att_duty(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                                                                     
                        
                        assert concl_future_att_duty_is_higher_than_rcvd_att_duty_body(dvc, attestation_duty); 
                        assert concl_future_att_duty_is_higher_than_queued_att_duty_body(dvc, attestation_duty);                                             
                        lemma_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_serve_attestation_duty(dvc, attestation_duty, dvc');    
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lemma_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
                       
                    case ImportedNewBlock(block) =>                     
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lemma_inv5_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv5_body(dvc_mod);
                        lemma_inv_strictly_increasing_queue_of_att_duties_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_strictly_increasing_queue_of_att_duties_body(dvc_mod);
                        lemma_inv_queued_att_duty_is_higher_than_latest_served_att_duty_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(dvc_mod);

                        lemma_inv_queued_att_duty_is_higher_than_latest_served_att_duty_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(dvc');
                    
                    case ResendAttestationShares =>                                                                                      

                    case NoEvent => 
                        
                }
                assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(dvc');

                forall n | n in dv'.honest_nodes_states.Keys 
                ensures inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(dv'.honest_nodes_states[n]);
                {
                    if n != node 
                    {
                        assert dv.honest_nodes_states[n] == dv'.honest_nodes_states[n];
                        assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(dv'.honest_nodes_states[n]);
                    }
                }                
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                forall n | n in dv'.honest_nodes_states.Keys 
                ensures inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(dv'.honest_nodes_states[n]);
                {
                    assert dv.honest_nodes_states[n] == dv'.honest_nodes_states[n];
                    assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(dv'.honest_nodes_states[n]);
                }   
                
        }   
    }  
    
}