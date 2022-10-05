include "../../../common/commons.dfy"
include "../common/attestation_creation_instrumented.dfy"
include "../../../specs/consensus/consensus.dfy"
include "../../../specs/network/network.dfy"
include "../../../specs/dvn/dvn.dfy"
include "inv.dfy"
include "fnc_invs_1_26.dfy"
include "../../common/helper_sets_lemmas.dfy"
include "proofs_intermediate_steps.dfy"

module DVN_Next_Invs_1_7
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

    lemma lemma_inv1_dvn_next(dvn: DVState, event: DV.Event, dvn': DVState)       
    requires NextEventPreCond(dvn, event)
    requires NextEvent(dvn, event, dvn')  
    requires inv1(dvn)
    ensures inv1(dvn')
    { }    

    lemma lemma_inv2_dvn_next(dvn: DVState, event: DV.Event, dvn': DVState)       
    requires NextEventPreCond(dvn, event)
    requires NextEvent(dvn, event, dvn')  
    requires inv2(dvn)
    ensures inv2(dvn')
    { }    

    lemma lemma_inv3_dvn_next(dvn: DVState, event: DV.Event, dvn': DVState)       
    requires NextEventPreCond(dvn, event)
    requires NextEvent(dvn, event, dvn')  
    requires inv3(dvn)
    ensures inv3(dvn')
    { }    

    lemma lemma_inv4_dvn_next_helper(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )
    requires inv1(dvn)    
    requires NextEventPreCond(dvn, event)
    requires NextEvent(dvn, event, dvn')  
    requires inv4(dvn)    
    requires event.HonestNodeTakingStep?
    requires dvn.honest_nodes_states[event.node].all_rcvd_duties == dvn'.honest_nodes_states[event.node].all_rcvd_duties
    ensures inv4(dvn')
    {

    }    

    lemma lemma_inv4_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )
    requires inv1(dvn)    
    requires NextEventPreCond(dvn, event)
    requires NextEvent(dvn, event, dvn')  
    requires inv4(dvn)
    ensures inv4(dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(att_duty) =>     
                        assert dvn'.index_next_attestation_duty_to_be_served 
                                    == dvn.index_next_attestation_duty_to_be_served + 1;
                        forall hn | hn in dvn.honest_nodes_states.Keys  
                        ensures inv4_body(hn, dvn'.honest_nodes_states[hn].all_rcvd_duties, dvn'.sequence_attestation_duties_to_be_served, dvn'.index_next_attestation_duty_to_be_served);                                                         
                        {
                            if hn != node 
                            {
                                
                                assert dvn.sequence_attestation_duties_to_be_served == dvn'.sequence_attestation_duties_to_be_served;                          
                                assert dvn'.honest_nodes_states[hn].all_rcvd_duties == dvn.honest_nodes_states[hn].all_rcvd_duties;                                                                  
                                
                                forall duty: AttestationDuty | duty in dvn'.honest_nodes_states[hn].all_rcvd_duties
                                ensures exists k: nat ::
                                                && k < dvn'.index_next_attestation_duty_to_be_served
                                                && dvn'.sequence_attestation_duties_to_be_served[k].node == hn
                                                && dvn'.sequence_attestation_duties_to_be_served[k].attestation_duty == duty
                                {
                                    var k: nat :| && k < dvn.index_next_attestation_duty_to_be_served
                                                  && dvn.sequence_attestation_duties_to_be_served[k].node == hn
                                                  && dvn.sequence_attestation_duties_to_be_served[k].attestation_duty == duty;

                                    assert && k < dvn'.index_next_attestation_duty_to_be_served
                                           && dvn'.sequence_attestation_duties_to_be_served[k].node == hn
                                           && dvn'.sequence_attestation_duties_to_be_served[k].attestation_duty == duty;
                                }
                                assert inv4_body(hn, dvn'.honest_nodes_states[hn].all_rcvd_duties, dvn'.sequence_attestation_duties_to_be_served, dvn'.index_next_attestation_duty_to_be_served);
                            }
                            else 
                            {                                   
                                var curr_index := dvn.index_next_attestation_duty_to_be_served;
                                var new_duty := dvn.sequence_attestation_duties_to_be_served[curr_index].attestation_duty;
                                lemma_inv4_f_serve_attestation_duty(dvc, new_duty, dvc');    
                                var new_duty_set := {new_duty};
                                assert dvc'.all_rcvd_duties == dvc.all_rcvd_duties + new_duty_set;                                                            
                                // assert new_duty in dvc'.all_rcvd_duties;                                                          

                                forall duty: AttestationDuty | duty in dvc'.all_rcvd_duties                                
                                ensures exists k: nat :: 
                                            && k < dvn'.index_next_attestation_duty_to_be_served
                                            && dvn'.sequence_attestation_duties_to_be_served[k].node == hn
                                            && dvn'.sequence_attestation_duties_to_be_served[k].attestation_duty == duty                                                                              
                                {   
                                    
                                    if duty == new_duty
                                    {                                                                                                                                                      
                                        assert && curr_index < dvn'.index_next_attestation_duty_to_be_served
                                               && dvn'.sequence_attestation_duties_to_be_served[curr_index].node == hn
                                               && dvn'.sequence_attestation_duties_to_be_served[curr_index].attestation_duty == duty;                                                                                
                                    }
                                    else
                                    {   
                                        lemmaInUnionOneElement(dvc'.all_rcvd_duties, dvc.all_rcvd_duties, new_duty, duty);  
                                        var k: nat :| && k < dvn.index_next_attestation_duty_to_be_served
                                                      && dvn.sequence_attestation_duties_to_be_served[k].node == hn
                                                      && dvn.sequence_attestation_duties_to_be_served[k].attestation_duty == duty;                                        
                                        
                                        assert && k < dvn'.index_next_attestation_duty_to_be_served
                                               && dvn'.sequence_attestation_duties_to_be_served[k].node == hn
                                               && dvn'.sequence_attestation_duties_to_be_served[k].attestation_duty == duty;
                                    }
                                }     

                                assert inv4_body(hn, dvn'.honest_nodes_states[hn].all_rcvd_duties, dvn'.sequence_attestation_duties_to_be_served, dvn'.index_next_attestation_duty_to_be_served); 
                                                   
                            }
                        }     
                        assert inv4(dvn');                   
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv4_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');    
                        assert inv4(dvn');                   
                        
                    case ReceviedAttesttionShare(attestation_share) =>                          
                        lemma_inv4_f_listen_for_attestation_shares(dvc, attestation_share, dvc');  
                        lemma_inv4_dvn_next_helper(dvn, event, dvn');                   
   
                    case ImportedNewBlock(block) => 
                        var dvc := add_block_to_bn(dvc, nodeEvent.block);
                        lemma_inv4_f_listen_for_new_imported_blocks(dvc, block, dvc');    
                        assert inv4(dvn');                    
                                                
                    case ResendAttestationShares => 
                        assert inv4(dvn');                        
                        
                    case NoEvent => 
                        assert inv4(dvn');
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                assert inv4(dvn');
                
        }        
    }   
    
    lemma lemma_inv5_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEventPreCond(dvn, event)
    requires NextEvent(dvn, event, dvn')  
    requires inv5(dvn)
    ensures inv5(dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>     
                        lemma_inv5_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv5_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                        
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
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

    lemma lemma_inv6_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEventPreCond(dvn, event)
    requires NextEvent(dvn, event, dvn')  
    requires inv5(dvn)
    requires inv6(dvn)
    ensures inv6(dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>     
                        lemma_inv6_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv6_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                        
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
                        lemma_inv6_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := add_block_to_bn(dvc, nodeEvent.block);
                        lemma_inv6_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendAttestationShares =>                         
                        
                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    } 

    lemma lemma_inv7_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEventPreCond(dvn, event)
    requires NextEvent(dvn, event, dvn')  
    requires inv5(dvn)
    requires inv7(dvn)
    ensures inv7(dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>     
                        lemma_inv7_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv7_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                        
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
                        lemma_inv7_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := add_block_to_bn(dvc, nodeEvent.block);
                        lemma_inv7_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendAttestationShares =>                         
                        
                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }  
}