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

module DV_Next_Invs_19_26
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

    lemma lemma_inv19_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')      
    requires inv19(dv')    
    ensures inv19(dv')    
    { }

    lemma lemma_inv20_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')      
    ensures inv20(dv, dv')
    { }

    lemma lemma_inv21_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )
    requires quorum_constraints(dv)    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv20(dv, dv')
    requires inv21(dv)
    ensures inv21(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(att_duty) =>     
                        var index := dv.index_next_attestation_duty_to_be_served;
                        var new_duty := dv.sequence_attestation_duties_to_be_served[index].attestation_duty;                                
                        lemma_inv4_f_serve_attestation_duty(dvc, new_duty, dvc');    
                        assert dvc'.all_rcvd_duties == dvc.all_rcvd_duties + {new_duty};                                                                                                       
                        var new_index := dv'.index_next_attestation_duty_to_be_served;
                        assert index + 1 == new_index;
                        
                        forall k: nat | ( && 0 <= k < new_index
                                          && dv'.sequence_attestation_duties_to_be_served[k].node in dv'.honest_nodes_states.Keys
                                        )    
                        ensures index + 1 == new_index
                        ensures dv'.sequence_attestation_duties_to_be_served[k].attestation_duty
                                    in dv'.honest_nodes_states[dv'.sequence_attestation_duties_to_be_served[k].node].all_rcvd_duties                            
                        {
                            var duty_and_node: AttestationDutyAndNode := dv.sequence_attestation_duties_to_be_served[k];
                            var duty := duty_and_node.attestation_duty;
                            var hn := duty_and_node.node;
                            var dvc_state := dv.honest_nodes_states[hn];
                            var dvc_state' := dv'.honest_nodes_states[hn];

                            if hn == node
                            {
                                if k < index
                                {     
                                    assert inv21_body(dvc_state, duty);
                                    assert inv21_body(dvc_state', duty);
                                }
                                else
                                {
                                    assert k == index;
                                    assert k == new_index - 1;
                                    lemma_inv4_f_serve_attestation_duty(dvc_state, att_duty, dvc_state');                                
                                    assert dvc'.all_rcvd_duties == dvc.all_rcvd_duties + {att_duty};
                                    assert att_duty in dvc'.all_rcvd_duties;                                
                                    assert inv21_body(dvc_state', duty);
                                }
                            }
                            else
                            {
                                assert dvc_state == dvc_state';
                                assert inv21_body(dvc_state', duty);
                            }
                            
                            assert inv21_body(dvc_state', duty);
                        }
                        
                        assert inv21(dv');

                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv4_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                        
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
                        lemma_inv4_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := add_block_to_bn(dvc, nodeEvent.block);
                        lemma_inv4_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendAttestationShares =>                         
                        
                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }        
    }   
    
    lemma lemma_inv22_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv22(dv)  
    ensures inv22(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                                                                     
                        lemma_inv22_f_serve_attestation_duty(dvc, attestation_duty, dvc');                                                
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv22_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
                        lemma_inv22_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lemma_inv22_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv22_body(dvc_mod);
                        lemma_inv22_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv22_body(dvc');
                    
                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    } 

    lemma lemma_inv23_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv5(dv)
    requires inv7(dv)
    requires inv13(dv)
    requires inv14(dv)
    requires inv17(dv)
    requires inv18(dv)
    requires inv22(dv)
    requires inv23(dv)  
    ensures inv23(dv')
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
                        assert inv7_body(dvc);                
                        assert inv14_body(dvc, attestation_duty);
                        assert inv17_body(dvc);
                        assert inv18_body(dvc);
                        assert inv22_body(dvc);
                        assert inv23_body(dvc);                                           
                        lemma_inv23_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv23_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        assert inv17_body(dvc);
                        assert inv18_body(dvc);
                        assert inv22_body(dvc);
                        lemma_inv23_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv23_body(dvc');
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
                        lemma_inv23_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv23_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        assert inv17_body(dvc);
                        assert inv18_body(dvc);
                        assert inv22_body(dvc);
                        
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lemma_inv17_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv17_body(dvc_mod);
                        lemma_inv18_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv18_body(dvc_mod);
                        lemma_inv22_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv22_body(dvc_mod);
                        lemma_inv23_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv23_body(dvc_mod);
                        lemma_inv23_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv23_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    } 
    
    lemma lemma_inv25_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv5(dv)
    requires inv25(dv)  
    ensures inv25(dv')
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
                        lemma_inv25_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv25_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv25_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv25_body(dvc');
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
                        lemma_inv25_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv25_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lemma_inv5_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv5_body(dvc_mod);
                        lemma_inv25_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv25_body(dvc_mod);
                        lemma_inv25_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv25_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    } 

    lemma lemma_inv26_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv5(dv)
    requires inv26(dv)  
    ensures inv26(dv')
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
                        lemma_inv26_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv26_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv26_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv26_body(dvc');
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
                        lemma_inv26_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv26_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lemma_inv5_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv5_body(dvc_mod);
                        lemma_inv26_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv26_body(dvc_mod);
                        lemma_inv26_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv26_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    } 

}   
        