include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"
include "../att_spec_proofs/dvc_ind_inv.dfy"
include "../att_spec_proofs/fnc_ind_inv.dfy"

module DVN_Next_Ind_Inv
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Att_Assumptions
    import opened DVN_Ind_Inv
    import opened Fnc_Ind_Inv

    lemma {:axiom} dvn_next_event_inv5_axiom(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEvent(dvn, e, dvn')        
    requires inv5(dvn)
    ensures inv5(dvn')

    lemma dvn_next_event_inv5(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEvent(dvn, e, dvn')        
    requires inv5(dvn)
    // ensures inv5(dvn')
    {
        if e.HonestNodeTakingStep?
        {
            var hn: BLSPubkey, hnEvent: Types.Event, hnOutputs: Outputs :| 
                        NextHonestNode(dvn, hn, hnEvent, hnOutputs, dvn');
            
            var s_w_honest_node_states_updated :|
                && ( if hnEvent.ImportedNewBlock? then 
                                     
                        s_w_honest_node_states_updated == 
                            dvn.(
                                honest_nodes_states := dvn.honest_nodes_states[hn := add_block_to_bn(dvn.honest_nodes_states[hn], hnEvent.block)]
                            )
                     
                     else 
                     
                        s_w_honest_node_states_updated == dvn
                     
                   )
                && NextHonestAfterAddingBlockToBn(s_w_honest_node_states_updated, hn, hnEvent, hnOutputs, dvn' )
                ;

            if hnEvent.ImportedNewBlock? 
            {
                assert s_w_honest_node_states_updated == 
                            dvn.(
                                honest_nodes_states := dvn.honest_nodes_states[hn := add_block_to_bn(dvn.honest_nodes_states[hn], hnEvent.block)]
                            );
                assert inv5(s_w_honest_node_states_updated);
            }                 
            else
            {
                assert s_w_honest_node_states_updated == dvn;
                assert inv5(s_w_honest_node_states_updated);
            }                    
                        
            assert inv5(s_w_honest_node_states_updated);     
           
            var hn_state := s_w_honest_node_states_updated.honest_nodes_states[hn];
            var hn_state' := dvn'.honest_nodes_states[hn];
            assert DVCNode_Spec.Next(hn_state, hnEvent, hn_state', hnOutputs);
            assert inv5_body(hn_state);
            dvc_next_inv5(hn_state, hn_state');
            assert inv5_body(hn_state');
           
            // dvn_next_event_inv5_axiom(dvn, e, dvn');
            // assert inv5(dvn');     
        }
        else
        {
            // dvn_next_event_inv5_axiom(dvn, e, dvn');
        }        
    }

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

    lemma {:axiom} assump_lemma_dvn_next_inv3(
        s': DVState
    )
    ensures inv3(s')

    lemma lemma_dvn_next_inv3(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )
    requires inv1(dvn)
    requires unchanged_fixed_paras(dvn, dvn')
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
                        forall hn | hn in dvn.honest_nodes_states.Keys                        
                        ensures forall duty: AttestationDuty 
                                    | 
                                    duty in dvn'.honest_nodes_states[hn].all_rcvd_duties
                                    ::
                                    exists k: nat :: 
                                        && dvn'.sequence_attestation_duties_to_be_served[k].node == hn
                                        && dvn'.sequence_attestation_duties_to_be_served[k].attestation_duty == duty
                                        
                        {
                            if hn != node 
                            {
                                assert dvn.sequence_attestation_duties_to_be_served == dvn'.sequence_attestation_duties_to_be_served;                          
                                assert dvn'.honest_nodes_states[hn].all_rcvd_duties == dvn.honest_nodes_states[hn].all_rcvd_duties;                                                                  
                                assert forall duty: AttestationDuty 
                                                | 
                                                duty in dvn'.honest_nodes_states[hn].all_rcvd_duties
                                                ::
                                                exists k: nat :: 
                                                    && dvn'.sequence_attestation_duties_to_be_served[k].node == hn
                                                    && dvn'.sequence_attestation_duties_to_be_served[k].attestation_duty == duty                              
                                ;                                                                                             
                            }
                            else 
                            {   
                                var curr_index := dvn.index_next_attestation_duty_to_be_served;
                                var new_duty := dvn.sequence_attestation_duties_to_be_served[curr_index].attestation_duty;
                                assert node == dvn.sequence_attestation_duties_to_be_served[curr_index].node;                        
                                lemma_f_serve_attestation_duty_inv3(dvc, new_duty, dvc');    
                                assert dvc'.all_rcvd_duties == dvc.all_rcvd_duties + {new_duty};                                                            
                                                                                          
                                forall duty: AttestationDuty | duty in dvn'.honest_nodes_states[hn].all_rcvd_duties
                                ensures exists k: nat :: 
                                                && dvn'.sequence_attestation_duties_to_be_served[k].node == hn
                                                && dvn'.sequence_attestation_duties_to_be_served[k].attestation_duty == duty                              
                                {
                                    if duty == new_duty
                                    {                                                                              
                                        assert && dvn'.sequence_attestation_duties_to_be_served[curr_index].node == hn
                                               && dvn'.sequence_attestation_duties_to_be_served[curr_index].attestation_duty == duty;
                                        
                                        assert exists k: nat :: 
                                                && dvn'.sequence_attestation_duties_to_be_served[k].node == hn
                                                && dvn'.sequence_attestation_duties_to_be_served[k].attestation_duty == duty;
                                    }
                                    else
                                    {                                        
                                        assert exists k: nat :: 
                                                && dvn'.sequence_attestation_duties_to_be_served[k].node == hn
                                                && dvn'.sequence_attestation_duties_to_be_served[k].attestation_duty == duty;
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