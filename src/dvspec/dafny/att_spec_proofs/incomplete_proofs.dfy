include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"
include "../att_spec_proofs/fnc_invs_1_26.dfy"
include "../att_spec_proofs/helper_sets_lemmas.dfy"
include "../att_spec_proofs/dvn_next_invs_1_7.dfy"
include "../att_spec_proofs/dvn_next_invs_8_18.dfy"
include "../att_spec_proofs/dvn_next_invs_19_26.dfy"
include "../att_spec_proofs/common_proofs.dfy"
include "../att_spec_proofs/fnc_invs_27.dfy"

module Incomplete_Proofs 
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB    
    import opened Helper_Sets_Lemmas
    import opened DVN_Next_Invs_1_7
    import opened DVN_Next_Invs_8_18
    import opened DVN_Next_Invs_19_26
    import opened Fnc_Invs_1_26    
    import opened Fnc_Invs_27
    import opened Common_Proofs
    

    lemma {:axiom} axiom_inv33(dvn: DVState)    
    ensures inv33(dvn)

    

 

    

 
    lemma lemma_inv33_ServeAttstationDuty(
        dvn: DVState,        
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')  
    requires event.HonestNodeTakingStep?
    requires event.event.ServeAttstationDuty?
    requires inv5(dvn)
    requires inv25(dvn)
    requires inv33(dvn)  
    // ensures inv33(dvn')
    {        

        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        forall hn: BLSPubkey | is_honest_node(dvn, hn)                             
                        {
                            
                            if hn == node
                            {
                                assert && dvc == dvn.honest_nodes_states[hn]
                                       && dvc' == dvn'.honest_nodes_states[hn];  

                                forall k: Slot | k in dvn'.consensus_on_attestation_data
                                {
                                    if hn in dvn'.consensus_on_attestation_data[k].honest_nodes_validity_functions.Keys
                                    {
                                        
                                    }
                                    else
                                    {
                                    
                                    }                                
                                }
                            }
                            else
                            {
                                calc {
                                    dvn.honest_nodes_states[hn];
                                    ==
                                    dvn'.honest_nodes_states[hn];                                      
                                } 

                                lemma_inv30_dvn_next(dvn, event, dvn');
                                assert inv30_body(dvn.honest_nodes_states[hn], dvn'.honest_nodes_states[hn]);

                                forall s: Slot | s in dvn'.consensus_on_attestation_data.Keys
                                {
                                    assert 
                                    hn in dvn'.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
                                    ==>
                                    hn in dvn.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys;
                                } 

                                forall s: Slot |
                                     hn in dvn'.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
                                // ensures
                                //    s in dvn'.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys
                                {
                                    assert hn in dvn.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys;
                                    assert dvn.consensus_on_attestation_data[s].honest_nodes_validity_functions[hn]
                                             == dvn'.consensus_on_attestation_data[s].honest_nodes_validity_functions[hn];
                                }
                                

                            
                            }
                        }
                }
        }
    }

/*
    lemma lemma_inv33_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')  
    requires inv5(dvn)
    requires inv25(dvn)
    requires inv33(dvn)  
    // ensures inv33(dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        forall hn: BLSPubkey, s: Slot | is_honest_node(dvn, hn)                             
                        // ensures inv33_body(dvn'.honest_nodes_states[hn], s);
                        {
                            if hn in dvn.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
                            {
                                if hn == node 
                                {
                                    assert inv5_body(dvn.honest_nodes_states[hn]);
                                    assert inv25_body(dvn.honest_nodes_states[hn]);
                                    assert inv33_body(dvn.honest_nodes_states[hn], s);
                                    lemma_inv33_f_serve_attestation_duty(
                                        dvn.honest_nodes_states[hn], 
                                        attestation_duty, 
                                        dvn'.honest_nodes_states[hn], 
                                        s);
                                    assert inv33_body(dvn'.honest_nodes_states[hn], s);
                                }
                                else
                                {
                                    assert dvn.honest_nodes_states[hn] == dvn'.honest_nodes_states[hn];
                                    assert inv33_body(dvn'.honest_nodes_states[hn], s);
                                }

                                
                            }
                            else
                            {
                                assert hn !in dvn.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys;
                            }
                        }
                        

                    case AttConsensusDecided(id, decided_attestation_data) => 
                    /*
                        forall hn: BLSPubkey, s: Slot | 
                            && is_honest_node(dvn, hn) 
                            && hn in dvn.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
                        ensures inv33_body(dvn'.honest_nodes_states[hn], s);
                        {
                            if hn == node 
                            {
                                assert inv5_body(dvc);
                                assert inv25_body(dvc);
                                assert inv33_body(dvc, s);
                                lemma_inv33_f_serve_attestation_duty(dvc, attestation_duty, dvc', s);
                                assert inv33_body(dvc', s);
                            }
                            else
                            {
                                assert dvn.honest_nodes_states[hn] == dvn'.honest_nodes_states[hn];
                                assert inv33_body(dvn'.honest_nodes_states[hn], s);
                            }
                        }
*/
                        // lemma_inv33_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        // assert inv33_body(dvc');
                        axiom_inv33(dvn');
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
                        // lemma_inv33_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        // assert inv33_body(dvc');
                       axiom_inv33(dvn');

                    case ImportedNewBlock(block) => 
                    /*
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lemma_inv5_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv5_body(dvc_mod);
                        lemma_inv33_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv33_body(dvc_mod);
                        lemma_inv33_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv33_body(dvc');
*/
                        axiom_inv33(dvn');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }  
    


    
*/
    

    
    
    

    

    
    

    

      
}