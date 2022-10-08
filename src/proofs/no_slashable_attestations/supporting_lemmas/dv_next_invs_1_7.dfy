include "../../../common/commons.dfy"
include "../common/attestation_creation_instrumented.dfy"
include "../../../specs/consensus/consensus.dfy"
include "../../../specs/network/network.dfy"
include "../../../specs/dv/dv_attestation_creation.dfy"
include "inv.dfy"
include "fnc_invs_1_26.dfy"
include "../../common/helper_sets_lemmas.dfy"
include "proofs_intermediate_steps.dfy"

module DV_Next_Invs_1_7
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

    lemma lemma_inv_quorum_constraints_dv_next(dv: DVState, event: DV.Event, dv': DVState)       
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_quorum_constraints(dv)
    ensures inv_quorum_constraints(dv')
    { }    

    lemma lemma_inv_unchanged_honesty_dv_next(dv: DVState, event: DV.Event, dv': DVState)       
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_unchanged_honesty(dv)
    ensures inv_unchanged_honesty(dv')
    { }    

    lemma lemma_inv_only_dv_construct_signed_attestation_signature_dv_next(dv: DVState, event: DV.Event, dv': DVState)       
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_only_dv_construct_signed_attestation_signature(dv)
    ensures inv_only_dv_construct_signed_attestation_signature(dv')
    { }    

    lemma lemma_inv4_dv_next_helper(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )
    requires inv_quorum_constraints(dv)    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv4(dv)    
    requires event.HonestNodeTakingStep?
    requires dv.honest_nodes_states[event.node].all_rcvd_duties == dv'.honest_nodes_states[event.node].all_rcvd_duties
    ensures inv4(dv')
    {

    }    

    lemma lemma_inv4_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )
    requires inv_quorum_constraints(dv)    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv4(dv)
    ensures inv4(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(att_duty) =>     
                        assert dv'.index_next_attestation_duty_to_be_served 
                                    == dv.index_next_attestation_duty_to_be_served + 1;
                        forall hn | hn in dv.honest_nodes_states.Keys  
                        ensures inv4_body(hn, dv'.honest_nodes_states[hn].all_rcvd_duties, dv'.sequence_attestation_duties_to_be_served, dv'.index_next_attestation_duty_to_be_served);                                                         
                        {
                            if hn != node 
                            {
                                
                                assert dv.sequence_attestation_duties_to_be_served == dv'.sequence_attestation_duties_to_be_served;                          
                                assert dv'.honest_nodes_states[hn].all_rcvd_duties == dv.honest_nodes_states[hn].all_rcvd_duties;                                                                  
                                
                                forall duty: AttestationDuty | duty in dv'.honest_nodes_states[hn].all_rcvd_duties
                                ensures exists k: nat ::
                                                && k < dv'.index_next_attestation_duty_to_be_served
                                                && dv'.sequence_attestation_duties_to_be_served[k].node == hn
                                                && dv'.sequence_attestation_duties_to_be_served[k].attestation_duty == duty
                                {
                                    var k: nat :| && k < dv.index_next_attestation_duty_to_be_served
                                                  && dv.sequence_attestation_duties_to_be_served[k].node == hn
                                                  && dv.sequence_attestation_duties_to_be_served[k].attestation_duty == duty;

                                    assert && k < dv'.index_next_attestation_duty_to_be_served
                                           && dv'.sequence_attestation_duties_to_be_served[k].node == hn
                                           && dv'.sequence_attestation_duties_to_be_served[k].attestation_duty == duty;
                                }
                                assert inv4_body(hn, dv'.honest_nodes_states[hn].all_rcvd_duties, dv'.sequence_attestation_duties_to_be_served, dv'.index_next_attestation_duty_to_be_served);
                            }
                            else 
                            {                                   
                                var curr_index := dv.index_next_attestation_duty_to_be_served;
                                var new_duty := dv.sequence_attestation_duties_to_be_served[curr_index].attestation_duty;
                                lemma_inv4_f_serve_attestation_duty(dvc, new_duty, dvc');    
                                var new_duty_set := {new_duty};
                                assert dvc'.all_rcvd_duties == dvc.all_rcvd_duties + new_duty_set;                                                            
                                // assert new_duty in dvc'.all_rcvd_duties;                                                          

                                forall duty: AttestationDuty | duty in dvc'.all_rcvd_duties                                
                                ensures exists k: nat :: 
                                            && k < dv'.index_next_attestation_duty_to_be_served
                                            && dv'.sequence_attestation_duties_to_be_served[k].node == hn
                                            && dv'.sequence_attestation_duties_to_be_served[k].attestation_duty == duty                                                                              
                                {   
                                    
                                    if duty == new_duty
                                    {                                                                                                                                                      
                                        assert && curr_index < dv'.index_next_attestation_duty_to_be_served
                                               && dv'.sequence_attestation_duties_to_be_served[curr_index].node == hn
                                               && dv'.sequence_attestation_duties_to_be_served[curr_index].attestation_duty == duty;                                                                                
                                    }
                                    else
                                    {   
                                        lemmaInUnionOneElement(dvc'.all_rcvd_duties, dvc.all_rcvd_duties, new_duty, duty);  
                                        var k: nat :| && k < dv.index_next_attestation_duty_to_be_served
                                                      && dv.sequence_attestation_duties_to_be_served[k].node == hn
                                                      && dv.sequence_attestation_duties_to_be_served[k].attestation_duty == duty;                                        
                                        
                                        assert && k < dv'.index_next_attestation_duty_to_be_served
                                               && dv'.sequence_attestation_duties_to_be_served[k].node == hn
                                               && dv'.sequence_attestation_duties_to_be_served[k].attestation_duty == duty;
                                    }
                                }     

                                assert inv4_body(hn, dv'.honest_nodes_states[hn].all_rcvd_duties, dv'.sequence_attestation_duties_to_be_served, dv'.index_next_attestation_duty_to_be_served); 
                                                   
                            }
                        }     
                        assert inv4(dv');                   
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv4_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');    
                        assert inv4(dv');                   
                        
                    case ReceivedAttestationShare(attestation_share) =>                          
                        lemma_inv4_f_listen_for_attestation_shares(dvc, attestation_share, dvc');  
                        lemma_inv4_dv_next_helper(dv, event, dv');                   
   
                    case ImportedNewBlock(block) => 
                        var dvc := add_block_to_bn(dvc, nodeEvent.block);
                        lemma_inv4_f_listen_for_new_imported_blocks(dvc, block, dvc');    
                        assert inv4(dv');                    
                                                
                    case ResendAttestationShares => 
                        assert inv4(dv');                        
                        
                    case NoEvent => 
                        assert inv4(dv');
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                assert inv4(dv');
                
        }        
    }   
    
    lemma lemma_inv5_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv5(dv)
    ensures inv5(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>     
                        lemma_inv5_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv5_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                        
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lemma_inv5_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := add_block_to_bn(dvc, nodeEvent.block);
                        lemma_inv5_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendAttestationShares =>                         
                        
                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }

    lemma lemma_inv_current_att_duty_is_rcvd_duty_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv5(dv)
    requires inv_current_att_duty_is_rcvd_duty(dv)
    ensures inv_current_att_duty_is_rcvd_duty(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>     
                        lemma_inv_current_att_duty_is_rcvd_duty_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv_current_att_duty_is_rcvd_duty_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                        
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lemma_inv_current_att_duty_is_rcvd_duty_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := add_block_to_bn(dvc, nodeEvent.block);
                        lemma_inv_current_att_duty_is_rcvd_duty_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendAttestationShares =>                         
                        
                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    } 

    lemma lemma_inv_latest_served_duty_is_rcvd_duty_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv5(dv)
    requires inv_latest_served_duty_is_rcvd_duty(dv)
    ensures inv_latest_served_duty_is_rcvd_duty(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>     
                        lemma_inv_latest_served_duty_is_rcvd_duty_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv_latest_served_duty_is_rcvd_duty_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                        
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lemma_inv_latest_served_duty_is_rcvd_duty_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := add_block_to_bn(dvc, nodeEvent.block);
                        lemma_inv_latest_served_duty_is_rcvd_duty_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendAttestationShares =>                         
                        
                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }  
}