include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"
include "../att_spec_proofs/fnc_invs_1_26.dfy"
include "../att_spec_proofs/helper_sets_lemmas.dfy"
include "../att_spec_proofs/proofs_intermediate_steps.dfy"
include "../att_spec_proofs/dvn_next_invs_1_7.dfy"
include "../att_spec_proofs/dvn_next_invs_8_18.dfy"
include "../att_spec_proofs/dvn_next_invs_19_26.dfy"
include "../att_spec_proofs/fnc_invs_27.dfy"

module DVN_Next_Invs_27
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Att_Assumptions
    import opened Fnc_Invs_1_26
    import opened Helper_Sets_Lemmas
    import opened Proofs_Intermediate_Steps
    import opened DVN_Next_Invs_1_7
    import opened DVN_Next_Invs_8_18
    import opened DVN_Next_Invs_19_26
    import opened Fnc_Invs_27
    

    lemma lemma_inv27_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')  
    requires inv5(dvn)
    requires inv25(dvn)
    requires inv27(dvn)  
    ensures inv27(dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        assert inv5_body(dvc);
                        assert inv25_body(dvc);   
                        assert inv27_body(dvc);                                           
                        lemma_inv27_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv27_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv27_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv27_body(dvc');
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
                        lemma_inv27_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv27_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lemma_inv5_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv5_body(dvc_mod);
                        lemma_inv27_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv27_body(dvc_mod);
                        lemma_inv27_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv27_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }

    lemma lemma_inv28_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')  
    requires inv5(dvn)
    requires inv26(dvn)
    requires inv28(dvn)  
    ensures inv28(dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        assert inv5_body(dvc);
                        assert inv26_body(dvc);   
                        assert inv28_body(dvc);                                           
                        lemma_inv28_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv28_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv28_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv28_body(dvc');
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
                        lemma_inv28_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv28_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lemma_inv5_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv5_body(dvc_mod);
                        lemma_inv28_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv28_body(dvc_mod);
                        lemma_inv28_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv28_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }

    lemma lemma_inv29_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')  
    requires inv5(dvn)
    requires inv25(dvn)
    requires inv29(dvn)  
    ensures inv29(dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        assert inv5_body(dvc);
                        assert inv25_body(dvc);   
                        assert inv29_body(dvc);                                           
                        lemma_inv29_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv29_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv29_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv29_body(dvc');
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
                        lemma_inv29_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv29_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lemma_inv5_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv5_body(dvc_mod);
                        lemma_inv29_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv29_body(dvc_mod);
                        lemma_inv29_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv29_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }

    lemma lemma_inv30_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')  
    ensures inv30(dvn, event, dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        lemma_inv30_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv30_body(dvc, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv30_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv30_body(dvc, dvc');
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
                        lemma_inv30_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv30_body(dvc, dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lemma_inv30_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv30_body(dvc, dvc_mod);
                        lemma_inv30_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv30_body(dvc_mod, dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }

    lemma lemma_inv31_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')  
    requires inv5(dvn)
    requires inv26(dvn)
    requires inv31(dvn)  
    ensures inv31(dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        assert inv5_body(dvc);
                        assert inv26_body(dvc);   
                        assert inv31_body(dvc);                                           
                        lemma_inv31_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv31_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv31_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv31_body(dvc');
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
                        lemma_inv31_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv31_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lemma_inv5_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv5_body(dvc_mod);
                        lemma_inv31_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv31_body(dvc_mod);
                        lemma_inv31_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv31_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }

    lemma lemma_inv32_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')  
    ensures inv32(dvn, event, dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        lemma_inv32_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv32_body(dvc, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv32_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv32_body(dvc, dvc');
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
                        lemma_inv32_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv32_body(dvc, dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lemma_inv32_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv32_body(dvc, dvc_mod);
                        lemma_inv32_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv32_body(dvc_mod, dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }

    

    lemma lemma_inv34_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')  
    requires inv34(dvn)
    ensures inv34(dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        lemma_inv34_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv34_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv34_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv34_body(dvc');
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
                        lemma_inv34_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv34_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lemma_inv34_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv34_body(dvc_mod);
                        lemma_inv34_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv34_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }

    lemma lemma_inv35_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')  
    requires inv35(dvn)
    ensures inv35(dvn')    
    {
        assert dvn.construct_signed_attestation_signature == dvn'.construct_signed_attestation_signature;
    }

    lemma lemma_inv36_body_network_spec_next<M>(
        e: Network<M>,
        e': Network<M>,
        n: BLSPubkey,
        messagesToBeSent: set<MessaageWithRecipient<M>>,
        messagesReceived: set<M>
    )
    requires NetworkSpec.Next(e, e', n, messagesToBeSent, messagesReceived)
    requires inv36_body(e)
    ensures inv36_body(e')
    {}

    

    lemma lemma_inv36_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')  
    requires inv36(dvn)
    ensures inv36(dvn')    
    {
        var n: BLSPubkey,
            messagesToBeSent: set<MessaageWithRecipient<AttestationShare>>,
            messagesReceived: set<AttestationShare> 
            :|
            NetworkSpec.Next<AttestationShare>(
                dvn.att_network, 
                dvn'.att_network, 
                n, 
                messagesToBeSent, 
                messagesReceived);

        lemma_inv36_body_network_spec_next<AttestationShare>(
                dvn.att_network, 
                dvn'.att_network, 
                n, 
                messagesToBeSent, 
                messagesReceived);  
    }

    lemma lemma_inv36_invNetwork(dvn: DVState)
    requires inv36(dvn)
    ensures invNetwork(dvn)
    {}

    lemma lemma_inv37_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )       
    requires NextEvent(dvn, event, dvn')
    requires inv37(dvn)
    ensures inv37(dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(att_duty) =>     
                        lemma_inv37_f_serve_attestation_duty(dvc, att_duty, dvc');
                        
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv37_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                        
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
                        lemma_inv37_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                                                

                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lemma_inv37_add_block_to_bn(dvc, block, dvc_mod);
                        lemma_inv37_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                                                
                                                
                    case ResendAttestationShares =>                         
                        lemma_inv37_f_resend_attestation_share(dvc, dvc');

                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }        
    }  
}   
        