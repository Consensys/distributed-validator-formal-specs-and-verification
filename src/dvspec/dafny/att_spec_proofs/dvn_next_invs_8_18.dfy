include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"
include "../att_spec_proofs/fnc_inv.dfy"
include "../att_spec_proofs/helper_sets_lemmas.dfy"
include "../att_spec_proofs/proofs_intermediate_steps.dfy"
include "../att_spec_proofs/dvn_next_invs_1_7.dfy"

module DVN_Next_Invs_8_18
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Att_Assumptions
    import opened Fnc_Inv
    import opened Helper_Sets_Lemmas
    import opened Proofs_Intermediate_Steps
    import opened DVN_Next_Invs_1_7

     

    lemma lemma_inv8_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')    
    requires inv8(dvn)
    ensures inv8(dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];
                assert inv8_body(dvc);
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                             
                        lemma_inv8_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv8_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
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

    lemma lemma_inv9_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')    
    requires inv9(dvn)
    ensures inv9(dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];
                assert inv9_body(dvc);
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                             
                        lemma_inv9_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv9_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
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

    lemma lemma_inv10_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')        
    requires inv10(dvn)
    ensures inv10(dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];
                assert inv10_body(dvc);
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                             
                        lemma_inv10_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv10_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
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

    
    lemma lemma_inv13_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')    
    requires inv13(dvn)
    ensures inv13(dvn)
    { }
    

    // It takes more than 60 seconds to prove lemma_inv16_dvn_next.
    lemma lemma_inv16_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')    
    requires inv8(dvn)
    requires inv16(dvn)
    ensures inv16(dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];
                assert inv16_body(dvc);
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                             
                        lemma_inv16_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv16_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
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

    lemma lemma_inv17_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')  
    requires inv1(dvn)  
    requires inv2(dvn)
    requires inv4(dvn)
    requires inv5(dvn)
    requires inv13(dvn)
    requires inv15(dvn)
    requires inv17(dvn)
    ensures inv17(dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];
                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                                                                     
                        lemma_inv17_f_serve_attestation_duty(dvc, attestation_duty, dvc');                                                
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv17_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
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
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }  

    lemma lemma_inv18_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')  
    requires inv1(dvn)  
    requires inv2(dvn)  
    requires inv4(dvn)
    requires inv5(dvn)
    requires inv7(dvn)
    requires inv13(dvn)  
    requires inv17(dvn)
    requires inv18(dvn)
    ensures inv18(dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                                                                     
                        
                        assert inv14_body(dvc, attestation_duty); 
                        assert inv15_body(dvc, attestation_duty);                                             
                        lemma_inv18_f_serve_attestation_duty(dvc, attestation_duty, dvc');    
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv18_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
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
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }  
    
}