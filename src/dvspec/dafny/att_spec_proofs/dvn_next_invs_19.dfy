include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"
include "../att_spec_proofs/fnc_inv.dfy"
include "../att_spec_proofs/helper_sets_lemmas.dfy"
include "../att_spec_proofs/proofs_intermediate_steps.dfy"
include "../att_spec_proofs/dvn_next_invs_1_7.dfy"
include "../att_spec_proofs/dvn_next_invs_8_18.dfy"

module DVN_Next_Invs_19
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
    import opened Proofs_Intermediate_Steps
    import opened DVN_Next_Invs_1_7
    import opened DVN_Next_Invs_8_18

    lemma lemma_inv19_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')    
    requires inv19(dvn')    
    ensures inv19(dvn')    
    { }

    lemma lemma_inv20_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )    
    requires NextEvent(dvn, event, dvn')    
    ensures inv20(dvn, dvn')
    { }

    lemma lemma_inv21_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )
    requires inv1(dvn)    
    requires NextEvent(dvn, event, dvn')
    requires inv20(dvn, dvn')
    requires inv21(dvn)
    ensures inv21(dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(att_duty) =>     
                        var index := dvn.index_next_attestation_duty_to_be_served;
                        var new_duty := dvn.sequence_attestation_duties_to_be_served[index].attestation_duty;                                
                        lemma_inv4_f_serve_attestation_duty(dvc, new_duty, dvc');    
                        assert dvc'.all_rcvd_duties == dvc.all_rcvd_duties + {new_duty};                                                                                                       
                        var new_index := dvn'.index_next_attestation_duty_to_be_served;
                        assert index + 1 == new_index;
                        
                        forall k: nat | ( && 0 <= k < new_index
                                          && dvn'.sequence_attestation_duties_to_be_served[k].node in dvn'.honest_nodes_states.Keys
                                        )    
                        ensures index + 1 == new_index
                        ensures dvn'.sequence_attestation_duties_to_be_served[k].attestation_duty
                                    in dvn'.honest_nodes_states[dvn'.sequence_attestation_duties_to_be_served[k].node].all_rcvd_duties                            
                        {
                            var duty_and_node: AttestationDutyAndNode := dvn.sequence_attestation_duties_to_be_served[k];
                            var duty := duty_and_node.attestation_duty;
                            var hn := duty_and_node.node;
                            var dvc_state := dvn.honest_nodes_states[hn];
                            var dvc_state' := dvn'.honest_nodes_states[hn];

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
                        
                        assert inv21(dvn');

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
    
    
}   
        