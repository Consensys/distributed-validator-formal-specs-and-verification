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

     

    lemma lemma_inv8_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')      
    requires inv8(dv)
    ensures inv8(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                assert inv8_body(dvc);
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                             
                        lemma_inv8_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv8_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lemma_inv8_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, nodeEvent.block);
                        lemma_inv8_add_block_to_bn(dvc, nodeEvent.block, dvc_mod);
                        assert inv8_body(dvc_mod);
                        lemma_inv8_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv8_body(dvc');
                        
                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }  

    lemma lemma_inv9_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')      
    requires inv9(dv)
    ensures inv9(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                assert inv9_body(dvc);
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                             
                        lemma_inv9_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv9_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lemma_inv9_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, nodeEvent.block);
                        lemma_inv9_add_block_to_bn(dvc, nodeEvent.block, dvc_mod);
                        assert inv9_body(dvc_mod);
                        lemma_inv9_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv9_body(dvc');
                        
                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }  

    lemma lemma_inv10_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')          
    requires inv10(dv)
    ensures inv10(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                assert inv10_body(dvc);
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                             
                        lemma_inv10_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv10_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lemma_inv10_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, nodeEvent.block);
                        lemma_inv10_add_block_to_bn(dvc, nodeEvent.block, dvc_mod);
                        assert inv10_body(dvc_mod);
                        lemma_inv10_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv10_body(dvc');
                        
                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }  

    
    lemma lemma_inv13_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')      
    requires inv13(dv)
    ensures inv13(dv')
    { 
        assert dv.sequence_attestation_duties_to_be_served == dv'.sequence_attestation_duties_to_be_served;
    }
    

    // It takes more than 60 seconds to prove lemma_inv16_dv_next.
    lemma lemma_inv16_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')      
    requires inv8(dv)
    requires inv16(dv)
    ensures inv16(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                assert inv16_body(dvc);
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                             
                        lemma_inv16_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv16_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lemma_inv16_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, nodeEvent.block);
                        lemma_inv16_add_block_to_bn(dvc, nodeEvent.block, dvc_mod);
                        assert inv16_body(dvc_mod);
                        lemma_inv16_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv16_body(dvc');
                        
                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }  

    lemma lemma_inv17_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires quorum_constraints(dv)  
    requires unchanged_honesty(dv)
    requires inv4(dv)
    requires inv5(dv)
    requires inv13(dv)
    requires inv15(dv)
    requires inv17(dv)
    ensures inv17(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                                                                     
                        lemma_inv17_f_serve_attestation_duty(dvc, attestation_duty, dvc');                                                
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv17_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lemma_inv17_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lemma_inv17_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv17_body(dvc_mod);
                        lemma_inv17_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv17_body(dvc');
                    
                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                assert inv17_body(dvc');
                forall n | n in dv'.honest_nodes_states.Keys 
                ensures inv17_body(dv'.honest_nodes_states[n]);
                {
                    if n != node 
                    {
                        assert dv.honest_nodes_states[n] == dv'.honest_nodes_states[n];
                        assert inv17_body(dv'.honest_nodes_states[n]);
                    }
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                assert inv17(dv');
                
        }   
    }  

    lemma lemma_inv18_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires quorum_constraints(dv)  
    requires unchanged_honesty(dv)  
    requires inv4(dv)
    requires inv5(dv)
    requires inv7(dv)
    requires inv13(dv)  
    requires inv17(dv)
    requires inv18(dv)
    ensures inv18(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                                                                     
                        
                        assert inv14_body(dvc, attestation_duty); 
                        assert inv15_body(dvc, attestation_duty);                                             
                        lemma_inv18_f_serve_attestation_duty(dvc, attestation_duty, dvc');    
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv18_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lemma_inv18_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
                       
                    case ImportedNewBlock(block) =>                     
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lemma_inv5_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv5_body(dvc_mod);
                        lemma_inv17_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv17_body(dvc_mod);
                        lemma_inv18_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv18_body(dvc_mod);

                        lemma_inv18_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv18_body(dvc');
                    
                    case ResendAttestationShares =>                                                                                      

                    case NoEvent => 
                        
                }
                assert inv18_body(dvc');

                forall n | n in dv'.honest_nodes_states.Keys 
                ensures inv18_body(dv'.honest_nodes_states[n]);
                {
                    if n != node 
                    {
                        assert dv.honest_nodes_states[n] == dv'.honest_nodes_states[n];
                        assert inv18_body(dv'.honest_nodes_states[n]);
                    }
                }                
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                forall n | n in dv'.honest_nodes_states.Keys 
                ensures inv18_body(dv'.honest_nodes_states[n]);
                {
                    assert dv.honest_nodes_states[n] == dv'.honest_nodes_states[n];
                    assert inv18_body(dv'.honest_nodes_states[n]);
                }   
                
        }   
    }  
    
}