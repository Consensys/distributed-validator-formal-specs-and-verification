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
include "dv_next_invs_8_18.dfy"
include "dv_next_invs_19_26.dfy"
include "fnc_invs_27_39.dfy"
include "ind_inv.dfy"
include "../common/dvc_spec_axioms.dfy"

module DV_Next_Invs_27_37
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Fnc_Invs_1_26
    import opened Helper_Sets_Lemmas
    import opened Proofs_Intermediate_Steps
    import opened DV_Next_Invs_1_7
    import opened DV_Next_Invs_8_18
    import opened DV_Next_Invs_19_26
    import opened Fnc_Invs_27_39
    import opened Att_Ind_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened DVCNode_Spec_Axioms
    

    lemma lemma_inv27_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv5(dv)
    requires inv25(dv)
    requires inv27(dv)  
    ensures inv27(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
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
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
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

    lemma lemma_inv28_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv5(dv)
    requires inv26(dv)
    requires inv28(dv)  
    ensures inv28(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
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
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
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

    lemma lemma_inv29_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv5(dv)
    requires inv25(dv)
    requires inv29(dv)  
    ensures inv29(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
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
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
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

    lemma lemma_inv30_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    ensures inv30(dv, event, dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        lemma_inv30_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv30_body(dvc, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv30_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv30_body(dvc, dvc');
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
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

    lemma lemma_inv31_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv5(dv)
    requires inv26(dv)
    requires inv31(dv)  
    ensures inv31(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
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
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
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

    lemma lemma_inv32_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    ensures inv32(dv, event, dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        lemma_inv32_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv32_body(dvc, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv32_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv32_body(dvc, dvc');
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
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

    

    lemma lemma_inv34_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv34(dv)
    ensures inv34(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        lemma_inv34_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv34_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv34_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv34_body(dvc');
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
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

    lemma lemma_inv35_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv35(dv)
    ensures inv35(dv')    
    {
        assert dv.construct_signed_attestation_signature == dv'.construct_signed_attestation_signature;
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

    

    lemma lemma_inv36_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv36(dv)
    ensures inv36(dv')    
    {
        var n: BLSPubkey,
            messagesToBeSent: set<MessaageWithRecipient<AttestationShare>>,
            messagesReceived: set<AttestationShare> 
            :|
            NetworkSpec.Next<AttestationShare>(
                dv.att_network, 
                dv'.att_network, 
                n, 
                messagesToBeSent, 
                messagesReceived);

        lemma_inv36_body_network_spec_next<AttestationShare>(
                dv.att_network, 
                dv'.att_network, 
                n, 
                messagesToBeSent, 
                messagesReceived);  
    }

    lemma lemma_inv36_invNetwork(dv: DVState)
    requires inv36(dv)
    ensures invNetwork(dv)
    {}

    lemma lemma_inv38_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )       
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires quorum_constraints(dv)
    requires inv2(dv)
    requires inv3(dv)
    requires inv53(dv)    
    requires pred_4_1_f_a(dv)    
    requires pred_4_1_g_i(dv)
    requires pred_4_1_g_i_for_dvc(dv)      
    requires pred_4_1_f_b(dv)       
    requires inv38(dv)    
    ensures inv38(dv')
    {   
        lemma_inv1_dv_next(dv, event, dv');
        lemma_inv2_dv_next(dv, event, dv');
        lemma_inv3_dv_next(dv, event, dv');

        assert && quorum_constraints(dv')
               && inv2(dv')
               && inv3(dv');
        

        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                assert && dvc.peers == dvc'.peers
                       && |dvc.peers| > 0 ;

                match nodeEvent
                {
                    case ServeAttstationDuty(att_duty) =>     
                        lemma_inv38_f_serve_attestation_duty(dvc, att_duty, dvc');                        
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        var att_network := dv.att_network;
                        var att_network' := dv'.att_network;
                        lemma_pred_4_1_g_iii_helper6(dv, event, dv');
                        lemma_inv38_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc', nodeOutputs);   
                        assert      att_network'.allMessagesSent
                                ==  att_network.allMessagesSent + getMessagesFromMessagesWithRecipient(nodeOutputs.att_shares_sent);               
                    
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lemma_inv38_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                                                

                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lemma_inv38_add_block_to_bn(dvc, block, dvc_mod);
                        lemma_inv38_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                                                
                                                
                    case ResendAttestationShares =>                         
                        lemma_inv38_f_resend_attestation_share(dvc, dvc');

                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }        
    }  

    lemma lemma_inv39_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )       
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    ensures dv.att_network.allMessagesSent <= dv'.att_network.allMessagesSent
    {}

    lemma lemma_inv37_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )       
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv36(dv)
    requires inv37(dv)
    ensures inv37(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(att_duty) =>     
                        lemma_inv37_f_serve_attestation_duty(dvc, att_duty, dvc');                        
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv37_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                        

                    case ReceivedAttestationShare(attestation_share) =>    
                        assert NetworkSpec.Next(dv.att_network, dv'.att_network, node, nodeOutputs.att_shares_sent, {attestation_share});
                        assert multiset(addReceipientToMessages<AttestationShare>({attestation_share}, node)) <= dv.att_network.messagesInTransit;
                        assert MessaageWithRecipient(message := attestation_share, receipient := node) in dv.att_network.messagesInTransit;        
                        assert attestation_share in dv.att_network.allMessagesSent;
                        assert attestation_share in dv'.att_network.allMessagesSent;
                        
                        lemma_inv39_dv_next(dv, event, dv');
                        assert dv.att_network.allMessagesSent <= dv'.att_network.allMessagesSent;
                        
                        lemma_inv37_f_listen_for_attestation_shares(dvc, attestation_share, dvc');  

                        assert dvc' == f_listen_for_attestation_shares(dvc, attestation_share).state;

                        var k := (attestation_share.data, attestation_share.aggregation_bits);
                        forall i, j | && i in dvc'.rcvd_attestation_shares.Keys 
                                      && j in dvc'.rcvd_attestation_shares[i].Keys
                        ensures dvc'.rcvd_attestation_shares[i][j] <= dv'.att_network.allMessagesSent;
                        {
                            if ( || i != attestation_share.data.slot
                                 || j != k
                               )
                            {             
                                lemma_inv37_f_listen_for_attestation_shares_domain(
                                    dvc,
                                    attestation_share,
                                    dvc'
                                );
                                assert && i in dvc.rcvd_attestation_shares.Keys 
                                       && j in dvc.rcvd_attestation_shares[i].Keys;
                                assert dvc'.rcvd_attestation_shares[i][j] <= dvc.rcvd_attestation_shares[i][j];                                
                                assert dvc.rcvd_attestation_shares[i][j] <= dv.att_network.allMessagesSent;
                                lemmaSubsetOfSubset(
                                    dvc'.rcvd_attestation_shares[i][j],
                                    dvc.rcvd_attestation_shares[i][j],
                                    dv.att_network.allMessagesSent
                                );
                                assert dv.att_network.allMessagesSent <= dv'.att_network.allMessagesSent;
                                lemmaSubsetOfSubset(
                                    dvc'.rcvd_attestation_shares[i][j],                                    
                                    dv.att_network.allMessagesSent,
                                    dv'.att_network.allMessagesSent
                                );
                                assert dvc'.rcvd_attestation_shares[i][j] <= dv'.att_network.allMessagesSent;
                            }
                            else
                            {
                                if  && i == attestation_share.data.slot
                                    && j == k
                                    && ( || i !in dvc.rcvd_attestation_shares.Keys
                                         || j !in dvc.rcvd_attestation_shares[i].Keys
                                       )                                       
                                {
                                    
                                    assert dvc'.rcvd_attestation_shares[i][j] <= {attestation_share};
                                    
                                    
                                    assert attestation_share in dv'.att_network.allMessagesSent;                                    
                                    lemmaFromMemberToSingletonSet(attestation_share, dv'.att_network.allMessagesSent);
                                    assert {attestation_share} <= dv'.att_network.allMessagesSent;

                                    lemmaSubsetOfSubset(
                                            dvc'.rcvd_attestation_shares[i][j],
                                            {attestation_share},
                                            dv'.att_network.allMessagesSent
                                        );
                                    assert dvc'.rcvd_attestation_shares[i][j] <= dv'.att_network.allMessagesSent;                                     
                                    
                                }
                                else
                                {
                                    assert  && i == attestation_share.data.slot
                                            && j == k
                                            && i in dvc.rcvd_attestation_shares.Keys 
                                            && j in dvc.rcvd_attestation_shares[i].Keys;

                                    
                                    assert dvc'.rcvd_attestation_shares[i][j] 
                                                <= dvc.rcvd_attestation_shares[i][j] + {attestation_share}; 

                                    assert dvc.rcvd_attestation_shares[i][j] 
                                                <= dv.att_network.allMessagesSent;                                                
                                    assert dv.att_network.allMessagesSent <= dv'.att_network.allMessagesSent;      
                                    lemmaSubsetOfSubset(
                                        dvc.rcvd_attestation_shares[i][j],
                                        dv.att_network.allMessagesSent,
                                        dv'.att_network.allMessagesSent);                                    
                                    assert dvc.rcvd_attestation_shares[i][j] 
                                                <= dv'.att_network.allMessagesSent;

                                    assert attestation_share in dv'.att_network.allMessagesSent;                                    
                                    lemmaFromMemberToSingletonSet(attestation_share, dv'.att_network.allMessagesSent);
                                    assert {attestation_share} <= dv'.att_network.allMessagesSent;

                                    lemmaUnionOfSubsets(dvc.rcvd_attestation_shares[i][j], {attestation_share}, dv'.att_network.allMessagesSent);                                    
                                    assert dvc.rcvd_attestation_shares[i][j] + {attestation_share}
                                                <= dv'.att_network.allMessagesSent;

                                    lemmaSubsetOfSubset(
                                        dvc'.rcvd_attestation_shares[i][j],
                                        dvc.rcvd_attestation_shares[i][j] + {attestation_share},
                                        dv'.att_network.allMessagesSent);
                                    
                                    assert dvc'.rcvd_attestation_shares[i][j] <= dv'.att_network.allMessagesSent;                                                                         
                                }
                            }
                        }
                        assert inv37(dv');

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

    lemma lemma_pred_4_1_g_iii_c_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEvent.requires(dv, event, dv')  
    requires NextEvent(dv, event, dv')  
    requires pred_4_1_g_iii_b(dv)
    requires pred_4_1_g_iii_c(dv)
    ensures pred_4_1_g_iii_c(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];   
                
                assert inv_g_iii_b_body_body(
                            dv,
                            node,
                            dvc,
                            dv.index_next_attestation_duty_to_be_served
                );

                assert inv_g_iii_b_new_body(
                            node,
                            dvc,
                            dv.sequence_attestation_duties_to_be_served,
                            dv.index_next_attestation_duty_to_be_served
                );

                assert inv_g_iii_c_body_body(
                            dv,
                            node,
                            dvc,
                            dv.index_next_attestation_duty_to_be_served
                );

                assert inv_g_iii_c_new_body(
                            node,
                            dvc,
                            dv.sequence_attestation_duties_to_be_served,
                            dv.index_next_attestation_duty_to_be_served
                );
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                           
                        lemma_pred_4_1_g_iii_c_f_serve_attestation_duty(
                            dvc, 
                            attestation_duty, 
                            dvc',
                            node,
                            dv.sequence_attestation_duties_to_be_served,
                            dv.index_next_attestation_duty_to_be_served
                        );
                        assert inv_g_iii_c_body_body(
                                    dv',
                                    node,
                                    dvc',
                                    dv'.index_next_attestation_duty_to_be_served
                        );
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_pred_4_1_g_iii_c_f_att_consensus_decided(
                            dvc, 
                            id, 
                            decided_attestation_data, 
                            dvc',
                            node,
                            dv.sequence_attestation_duties_to_be_served,
                            dv.index_next_attestation_duty_to_be_served);
                        assert inv_g_iii_c_body_body(
                                    dv',
                                    node,
                                    dvc',
                                    dv'.index_next_attestation_duty_to_be_served
                        );
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lemma_pred_4_1_g_iii_c_f_listen_for_attestation_shares(
                            dvc, 
                            attestation_share, 
                            dvc',
                            node,
                            dv.sequence_attestation_duties_to_be_served,
                            dv.index_next_attestation_duty_to_be_served);
                        assert inv_g_iii_c_body_body(
                                    dv',
                                    node,
                                    dvc',
                                    dv'.index_next_attestation_duty_to_be_served
                        );
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lemma_pred_4_1_g_iii_c_add_block_to_bn(
                            dvc, 
                            block, 
                            dvc_mod,
                            node,
                            dv.sequence_attestation_duties_to_be_served,
                            dv.index_next_attestation_duty_to_be_served
                        );
                        assert inv_g_iii_c_new_body(
                            node,
                            dvc_mod,
                            dv.sequence_attestation_duties_to_be_served,
                            dv.index_next_attestation_duty_to_be_served
                        );
                        lemma_pred_4_1_g_iii_c_f_listen_for_new_imported_blocks(
                            dvc_mod, 
                            block, 
                            dvc',
                            node,
                            dv.sequence_attestation_duties_to_be_served,
                            dv.index_next_attestation_duty_to_be_served
                        );
                        assert inv_g_iii_c_body_body(
                                    dv',
                                    node,
                                    dvc',
                                    dv'.index_next_attestation_duty_to_be_served
                        );

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }      
}   
        