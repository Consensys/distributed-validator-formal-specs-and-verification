include "../../../../common/commons.dfy"
include "../../common/attestation_creation_instrumented.dfy"
include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_attestation_creation.dfy"

include "../../../common/helper_sets_lemmas.dfy"
include "../../common/common_proofs.dfy"
include "../../common/dvc_spec_axioms.dfy"

include "../inv.dfy"

include "invs_fnc_1.dfy"

module Invs_DV_Next_1
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Fnc_Invs_1
    import opened Helper_Sets_Lemmas

    lemma lem_inv_all_honest_nodes_is_a_quorum_dv_next(dv: DVState, event: DV.Event, dv': DVState)       
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_all_honest_nodes_is_a_quorum(dv)
    ensures inv_all_honest_nodes_is_a_quorum(dv')
    { }    

    lemma lem_inv_unchanged_paras_of_consensus_instances_dv_next(dv: DVState, event: DV.Event, dv': DVState)       
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_unchanged_paras_of_consensus_instances(dv)
    ensures inv_unchanged_paras_of_consensus_instances(dv')
    { }    

    lemma lem_inv_only_dv_construct_signed_attestation_signature_dv_next(dv: DVState, event: DV.Event, dv': DVState)       
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_only_dv_construct_signed_attestation_signature(dv)
    ensures inv_only_dv_construct_signed_attestation_signature(dv')
    { }    

   

    lemma lem_inv_current_att_duty_is_rcvd_duty_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
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
                    case ServeAttestationDuty(attestation_duty) =>     
                        lem_inv_current_att_duty_is_rcvd_duty_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        if f_att_consensus_decided.requires(dvc, id, decided_attestation_data)
                        {
                            lem_inv_current_att_duty_is_rcvd_duty_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');      
                        }                 
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_current_att_duty_is_rcvd_duty_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_current_att_duty_is_rcvd_duty_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendAttestationShares =>                         
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
        }   
    } 

    lemma lem_inv_latest_att_duty_is_rcvd_duty_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_latest_att_duty_is_rcvd_duty(dv)
    ensures inv_latest_att_duty_is_rcvd_duty(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) =>     
                        lem_inv_latest_att_duty_is_rcvd_duty_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        if f_att_consensus_decided.requires(dvc, id, decided_attestation_data)
                        {
                            lem_inv_latest_att_duty_is_rcvd_duty_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                        
                        }

                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_latest_att_duty_is_rcvd_duty_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_latest_att_duty_is_rcvd_duty_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendAttestationShares =>                         
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
        }   
    }  

    lemma lem_inv_none_latest_att_duty_implies_none_current_att_duty_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')      
    requires inv_none_latest_att_duty_implies_none_current_att_duty(dv)
    ensures inv_none_latest_att_duty_implies_none_current_att_duty(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                assert inv_none_latest_att_duty_implies_none_current_att_duty_body(dvc);
                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) =>                             
                        lem_inv_none_latest_att_duty_implies_none_current_att_duty_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        if f_att_consensus_decided.requires(dvc, id, decided_attestation_data)
                        {
                            lem_inv_none_latest_att_duty_implies_none_current_att_duty_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        }

                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_none_latest_att_duty_implies_none_current_att_duty_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc_mod := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_none_latest_att_duty_implies_none_current_att_duty_add_block_to_bn(dvc, nodeEvent.block, dvc_mod);
                        assert inv_none_latest_att_duty_implies_none_current_att_duty_body(dvc_mod);
                        lem_inv_none_latest_att_duty_implies_none_current_att_duty_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_none_latest_att_duty_implies_none_current_att_duty_body(dvc');
                        
                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
        }   
    }  

    lemma lem_inv_current_att_duty_is_either_none_or_latest_att_duty_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')      
    requires inv_current_att_duty_is_either_none_or_latest_att_duty(dv)
    ensures inv_current_att_duty_is_either_none_or_latest_att_duty(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                assert inv_current_att_duty_is_either_none_or_latest_att_duty_body(dvc);
                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) =>                             
                        lem_inv_current_att_duty_is_either_none_or_latest_att_duty_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        if f_att_consensus_decided.requires(dvc, id, decided_attestation_data)
                        {
                            lem_inv_current_att_duty_is_either_none_or_latest_att_duty_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        }

                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_current_att_duty_is_either_none_or_latest_att_duty_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc_mod := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_current_att_duty_is_either_none_or_latest_att_duty_add_block_to_bn(dvc, nodeEvent.block, dvc_mod);
                        assert inv_current_att_duty_is_either_none_or_latest_att_duty_body(dvc_mod);
                        lem_inv_current_att_duty_is_either_none_or_latest_att_duty_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_current_att_duty_is_either_none_or_latest_att_duty_body(dvc');
                        
                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
        }   
    }  

    lemma lem_inv_available_current_att_duty_is_latest_att_duty_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')          
    requires inv_available_current_att_duty_is_latest_att_duty(dv)
    ensures inv_available_current_att_duty_is_latest_att_duty(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                assert inv_available_current_att_duty_is_latest_att_duty_body(dvc);
                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) =>                             
                        lem_inv_available_current_att_duty_is_latest_att_duty_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        if f_att_consensus_decided.requires(dvc, id, decided_attestation_data)
                        {
                            lem_inv_available_current_att_duty_is_latest_att_duty_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        }

                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_available_current_att_duty_is_latest_att_duty_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc_mod := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_available_current_att_duty_is_latest_att_duty_add_block_to_bn(dvc, nodeEvent.block, dvc_mod);
                        assert inv_available_current_att_duty_is_latest_att_duty_body(dvc_mod);
                        lem_inv_available_current_att_duty_is_latest_att_duty_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_available_current_att_duty_is_latest_att_duty_body(dvc');
                        
                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
        }   
    }  

    
    lemma lem_inv_the_sequence_of_att_duties_is_in_order_of_slots_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')      
    requires inv_the_sequence_of_att_duties_is_in_order_of_slots(dv)
    ensures inv_the_sequence_of_att_duties_is_in_order_of_slots(dv')
    { 
        assert dv.sequence_attestation_duties_to_be_served == dv'.sequence_attestation_duties_to_be_served;
    }
    

    lemma lem_inv_no_duplicated_att_duties_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')      
    requires inv_no_duplicated_att_duties(dv')    
    ensures inv_no_duplicated_att_duties(dv')    
    { }

    lemma lem_pred_unchanged_dvn_seq_of_att_duties_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')      
    ensures pred_unchanged_dvn_seq_of_att_duties(dv, dv')
    { }

    lemma lem_inv_every_att_duty_before_dvn_att_index_was_delivered_f_serve_attestation_duty(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )  
    requires inv_all_honest_nodes_is_a_quorum(dv)    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires event.HonestNodeTakingStep?
    requires pred_unchanged_dvn_seq_of_att_duties(dv, dv')
    requires inv_every_att_duty_before_dvn_att_index_was_delivered(dv)
    ensures inv_every_att_duty_before_dvn_att_index_was_delivered(dv')
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttestationDuty(att_duty) =>     
                        var index := dv.index_next_attestation_duty_to_be_served;
                        var new_duty := dv.sequence_attestation_duties_to_be_served[index].attestation_duty;                                
                        lem_updated_all_rcvd_duties_f_serve_attestation_duty(dvc, new_duty, dvc');   
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
                                    assert inv_every_att_duty_before_dvn_att_index_was_delivered_body(dvc_state, duty);
                                    assert inv_every_att_duty_before_dvn_att_index_was_delivered_body(dvc_state', duty);
                                }
                                else
                                {
                                    assert k == index;
                                    assert k == new_index - 1;
                                    lem_updated_all_rcvd_duties_f_serve_attestation_duty(dvc, new_duty, dvc');                                  
                                    assert dvc'.all_rcvd_duties == dvc.all_rcvd_duties + {att_duty};
                                    assert att_duty in dvc'.all_rcvd_duties;                                
                                    assert inv_every_att_duty_before_dvn_att_index_was_delivered_body(dvc_state', duty);
                                }
                            }
                            else
                            {
                                assert dvc_state == dvc_state';
                                assert inv_every_att_duty_before_dvn_att_index_was_delivered_body(dvc_state', duty);
                            }
                            
                            assert inv_every_att_duty_before_dvn_att_index_was_delivered_body(dvc_state', duty);
                        }
                        
                        assert inv_every_att_duty_before_dvn_att_index_was_delivered(dv');

                    case AttConsensusDecided(id, decided_attestation_data) => 
                        
                    case ReceivedAttestationShare(attestation_share) =>                         

                    case ImportedNewBlock(block) => 

                    case ResendAttestationShares =>         
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
        } 
    }


    lemma lem_inv_every_att_duty_before_dvn_att_index_was_delivered_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )
    requires inv_all_honest_nodes_is_a_quorum(dv)    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires pred_unchanged_dvn_seq_of_att_duties(dv, dv')
    requires inv_every_att_duty_before_dvn_att_index_was_delivered(dv)
    ensures inv_every_att_duty_before_dvn_att_index_was_delivered(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttestationDuty(att_duty) =>     
                        lem_inv_every_att_duty_before_dvn_att_index_was_delivered_f_serve_attestation_duty(
                                dv,
                                event,
                                dv'
                            );

                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_updated_all_rcvd_duties_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');    
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_updated_all_rcvd_duties_f_listen_for_attestation_shares(dvc, attestation_share, dvc');  

                    case ImportedNewBlock(block) => 
                        var dvc_mod := f_add_block_to_bn(dvc, block);
                        lem_updated_all_rcvd_duties_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');

                    case ResendAttestationShares =>         
                        lem_updated_all_rcvd_duties_f_resend_attestation_share(dvc, dvc');
                        
                    case NoEvent => 
                        
                }

            case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
        }        
    }   
    
    lemma lem_inv_no_active_consensus_instances_before_the_first_att_duty_was_received_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_no_active_consensus_instances_before_the_first_att_duty_was_received(dv)  
    ensures inv_no_active_consensus_instances_before_the_first_att_duty_was_received(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                
                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) =>                                                                     
                        lem_inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body_f_serve_attestation_duty(dvc, attestation_duty, dvc');                                                
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        if f_att_consensus_decided.requires(dvc, id, decided_attestation_data)
                        {
                            lem_inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        }

                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := f_add_block_to_bn(dvc, block);
                        lem_inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body_f_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(dvc_mod);
                        lem_inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(dvc');
                    
                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
        }   
    } 

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_latest_att_duty_is_rcvd_duty(dv)
    requires inv_the_sequence_of_att_duties_is_in_order_of_slots(dv)
    requires inv_an_att_duty_in_the_next_delivery_is_not_lower_than_rcvd_att_duties(dv)
    requires inv_no_active_consensus_instances_before_the_first_att_duty_was_received(dv)
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty(dv)  
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) =>   
                        assert inv_latest_att_duty_is_rcvd_duty_body(dvc);                
                        assert inv_an_att_duty_in_the_next_delivery_is_not_lower_than_rcvd_att_duties_body(dvc, attestation_duty);
                        assert inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(dvc);
                        assert inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(dvc);                                           
                        lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        if f_att_consensus_decided.requires(dvc, id, decided_attestation_data)
                        {
                            assert inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(dvc);
                            lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                            assert inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(dvc');
                        }

                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        assert inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(dvc);
                        
                        var dvc_mod := f_add_block_to_bn(dvc, block);
                        lem_inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body_f_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_no_active_consensus_instances_before_the_first_att_duty_was_received_body(dvc_mod);
                        lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body_f_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(dvc_mod);
                        lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_att_duty_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
        }   
    } 
    
    lemma lem_inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance(dv)  
    ensures inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) =>   
                        assert inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(dvc);                                           
                        lem_inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        if f_att_consensus_decided.requires(dvc, id, decided_attestation_data)
                        {
                            lem_inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                            assert inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(dvc');
                        }

                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := f_add_block_to_bn(dvc, block);
                        lem_inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body_f_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(dvc_mod);
                        lem_inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_dvc_has_a_corresponding_att_duty_for_every_active_attestation_consensus_instance_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
        }   
    } 

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k(dv)  
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) =>   
                        assert inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(dvc);                                           
                        lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        if f_att_consensus_decided.requires(dvc, id, decided_attestation_data)
                        {
                            lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                            assert inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(dvc');
                        }

                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := f_add_block_to_bn(dvc, block);
                        lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body_f_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(dvc_mod);
                        lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_at_slot_k_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
        }   
    }  
}