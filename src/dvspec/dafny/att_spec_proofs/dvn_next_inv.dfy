include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"
include "../att_spec_proofs/fnc_inv.dfy"
include "../att_spec_proofs/helper_sets_lemmas.dfy"

module DVN_Next_Inv
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

    

    lemma lemma_inv1_dvn_next(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    requires inv1(dvn)
    ensures inv1(dvn')
    { }

    lemma lemma_inv2_dvn_next(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    requires inv2(dvn)
    ensures inv2(dvn')
    { }

    lemma lemma_inv3_dvn_next(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    requires inv3(dvn)
    ensures inv3(dvn')
    { }

    // It takes more than 60 seconds to prove lemma_inv4_dvn_next.
    lemma lemma_inv4_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )
    requires inv1(dvn)    
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
                        ensures forall duty: AttestationDuty 
                                    | 
                                    duty in dvn'.honest_nodes_states[hn].all_rcvd_duties
                                    ::
                                    exists k: nat :: 
                                        && k < dvn'.index_next_attestation_duty_to_be_served
                                        && dvn'.sequence_attestation_duties_to_be_served[k].node == hn
                                        && dvn'.sequence_attestation_duties_to_be_served[k].attestation_duty == duty                                     
                        {
                            if hn != node 
                            {
                                
                                assert dvn.sequence_attestation_duties_to_be_served == dvn'.sequence_attestation_duties_to_be_served;                          
                                assert dvn'.honest_nodes_states[hn].all_rcvd_duties == dvn.honest_nodes_states[hn].all_rcvd_duties;                                                                  
                                
                                forall duty: AttestationDuty | duty in dvn.honest_nodes_states[hn].all_rcvd_duties
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
                            }
                            else 
                            {                                   
                                var curr_index := dvn.index_next_attestation_duty_to_be_served;
                                var new_duty := dvn.sequence_attestation_duties_to_be_served[curr_index].attestation_duty;
                                lemma_inv4_f_serve_attestation_duty(dvc, new_duty, dvc');    
                                assert dvc'.all_rcvd_duties == dvc.all_rcvd_duties + {new_duty};                                                            
                                assert new_duty in dvc'.all_rcvd_duties;                                                          

                                forall duty: AttestationDuty | duty in dvn'.honest_nodes_states[hn].all_rcvd_duties                                
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
                                        assert duty in dvc.all_rcvd_duties;                                        
                                        var k: nat :| && k < dvn.index_next_attestation_duty_to_be_served
                                                      && dvn.sequence_attestation_duties_to_be_served[k].node == hn
                                                      && dvn.sequence_attestation_duties_to_be_served[k].attestation_duty == duty;                                        
                                        
                                        assert && k < dvn'.index_next_attestation_duty_to_be_served
                                               && dvn'.sequence_attestation_duties_to_be_served[k].node == hn
                                               && dvn'.sequence_attestation_duties_to_be_served[k].attestation_duty == duty;
                                    }
                                }      
                                                   
                            }
                        }                        
                        
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
    
    lemma lemma_inv5_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
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

    // It takes more than 60 seconds to prove lemma_inv11_dvn_next.
    lemma lemma_inv11_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')    
    requires inv8(dvn)
    requires inv11(dvn)
    ensures inv11(dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];
                assert inv11_body(dvc);
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                             
                        lemma_inv11_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv11_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
                        lemma_inv11_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, nodeEvent.block);
                        lemma_inv11_add_block_to_bn(dvc, nodeEvent.block, dvc_mod);
                        assert inv11_body(dvc_mod);
                        lemma_inv11_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv11_body(dvc');
                        
                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }  

    

}