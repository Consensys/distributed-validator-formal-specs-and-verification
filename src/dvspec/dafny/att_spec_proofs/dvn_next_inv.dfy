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

    lemma lemma_dvn_next_inv1(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    requires inv1(dvn)
    ensures inv1(dvn')
    { }

    lemma lemma_dvn_next_inv2(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    requires inv2(dvn)
    ensures inv2(dvn')
    { }

    lemma lemma_dvn_next_inv3(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )
    requires inv1(dvn)
    requires NextEvent(dvn, event, dvn')
    requires inv3(dvn)
    ensures inv3(dvn')
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
                                }
                            }
                            else 
                            {                                   
                                var curr_index := dvn.index_next_attestation_duty_to_be_served;
                                var new_duty := dvn.sequence_attestation_duties_to_be_served[curr_index].attestation_duty;
                                lemma_f_serve_attestation_duty_inv3(dvc, new_duty, dvc');    
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
                                    }
                                }      
                                                   
                            }
                        }                        
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_f_att_consensus_decided_inv3(dvc, id, decided_attestation_data, dvc');                        
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
                        lemma_f_listen_for_attestation_shares_inv3(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := add_block_to_bn(dvc, nodeEvent.block);
                        lemma_f_listen_for_new_imported_blocks_inv3(dvc, block, dvc');                        
                                                
                    case ResendAttestationShares =>                         
                        
                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }        
    }   
    
    
 
}