include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"
include "../att_spec_proofs/dvc_ind_inv.dfy"

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

    lemma dvn_next_inv1(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    requires inv1(dvn)
    ensures inv1(dvn')
    { }

    lemma dvn_next_inv2(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    requires inv2(dvn)
    ensures inv2(dvn')
    { }

    lemma dvn_next_inv3(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    requires inv3(dvn)
    ensures inv3(dvn')
    { }

    lemma dvn_next_inv4(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    requires inv4(dvn)
    ensures inv4(dvn')
    { }

    
    
 
}