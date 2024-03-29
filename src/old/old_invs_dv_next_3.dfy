include "../../../common/commons.dfy"
include "../common/attestation_creation_instrumented.dfy"
include "../../../specs/consensus/consensus.dfy"
include "../../../specs/network/network.dfy"
include "../../../specs/dv/dv_attestation_creation.dfy"
include "inv.dfy"
include "invs_fnc_1.dfy"
include "../../common/helper_sets_lemmas.dfy"
include "proofs_intermediate_steps.dfy"
include "invs_dv_next_1.dfy"
include "invs_dv_next_1.dfy"

module DV_Next_Invs_19_26
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
    import opened Proofs_Intermediate_Steps
    import opened Invs_DV_Next_1
    import opened DV_Next_Invs_8_18

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

    lemma lem_concl_unchanged_dvn_seq_of_att_duties_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')      
    ensures concl_unchanged_dvn_seq_of_att_duties(dv, dv')
    { }

    lemma lem_inv_every_att_duty_before_dvn_att_index_was_delivered_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )
    requires inv_quorum_constraints(dv)    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires concl_unchanged_dvn_seq_of_att_duties(dv, dv')
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
                    case ServeAttstationDuty(att_duty) =>     
                        var index := dv.index_next_attestation_duty_to_be_served;
                        var new_duty := dv.sequence_attestation_duties_to_be_served[index].attestation_duty;                                
                        lem_inv_queued_att_duty_is_dvn_seq_of_att_duty_f_serve_attestation_duty(dvc, new_duty, dvc');    
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
                                    lem_inv_queued_att_duty_is_dvn_seq_of_att_duty_f_serve_attestation_duty(dvc_state, att_duty, dvc_state');                                
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
                        lem_inv_queued_att_duty_is_dvn_seq_of_att_duty_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                        
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_queued_att_duty_is_dvn_seq_of_att_duty_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
   
                    case ImportedNewBlock(block) => 
                        var dvc := add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_queued_att_duty_is_dvn_seq_of_att_duty_f_listen_for_new_imported_blocks(dvc, block, dvc');                        
                                                
                    case ResendAttestationShares =>                         
                        
                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }        
    }   
    
    lemma lem_inv_no_active_consensus_instance_before_receiving_att_duty_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_no_active_consensus_instance_before_receiving_att_duty(dv)  
    ensures inv_no_active_consensus_instance_before_receiving_att_duty(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                                                                     
                        lem_inv_no_active_consensus_instance_before_receiving_att_duty_f_serve_attestation_duty(dvc, attestation_duty, dvc');                                                
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_no_active_consensus_instance_before_receiving_att_duty_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                                                
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_no_active_consensus_instance_before_receiving_att_duty_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                        
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lem_inv_no_active_consensus_instance_before_receiving_att_duty_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_no_active_consensus_instance_before_receiving_att_duty_body(dvc_mod);
                        lem_inv_no_active_consensus_instance_before_receiving_att_duty_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_no_active_consensus_instance_before_receiving_att_duty_body(dvc');
                    
                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    } 

    lemma lem_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_queued_att_duty_is_rcvd_duty(dv)
    requires inv_latest_served_duty_is_rcvd_duty(dv)
    requires inv_is_sequence_attestation_duties_to_be_serves_orders(dv)
    requires concl_future_att_duty_is_higher_than_rcvd_att_duty(dv)
    requires inv_strictly_increasing_queue_of_att_duties(dv)
    requires inv_queued_att_duty_is_higher_than_latest_served_att_duty(dv)
    requires inv_no_active_consensus_instance_before_receiving_att_duty(dv)
    requires inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty(dv)  
    ensures inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        assert inv_queued_att_duty_is_rcvd_duty_body(dvc);
                        assert inv_latest_served_duty_is_rcvd_duty_body(dvc);                
                        assert concl_future_att_duty_is_higher_than_rcvd_att_duty_body(dvc, attestation_duty);
                        assert inv_strictly_increasing_queue_of_att_duties_body(dvc);
                        assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(dvc);
                        assert inv_no_active_consensus_instance_before_receiving_att_duty_body(dvc);
                        assert inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(dvc);                                           
                        lem_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        assert inv_strictly_increasing_queue_of_att_duties_body(dvc);
                        assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(dvc);
                        assert inv_no_active_consensus_instance_before_receiving_att_duty_body(dvc);
                        lem_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(dvc');
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        assert inv_strictly_increasing_queue_of_att_duties_body(dvc);
                        assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(dvc);
                        assert inv_no_active_consensus_instance_before_receiving_att_duty_body(dvc);
                        
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lem_inv_strictly_increasing_queue_of_att_duties_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_strictly_increasing_queue_of_att_duties_body(dvc_mod);
                        lem_inv_queued_att_duty_is_higher_than_latest_served_att_duty_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_queued_att_duty_is_higher_than_latest_served_att_duty_body(dvc_mod);
                        lem_inv_no_active_consensus_instance_before_receiving_att_duty_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_no_active_consensus_instance_before_receiving_att_duty_body(dvc_mod);
                        lem_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(dvc_mod);
                        lem_inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    } 
    
    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_queued_att_duty_is_rcvd_duty(dv)
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty(dv)  
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        assert inv_queued_att_duty_is_rcvd_duty_body(dvc);
                        assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(dvc);                                           
                        lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(dvc');
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lem_inv_queued_att_duty_is_rcvd_duty_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_queued_att_duty_is_rcvd_duty_body(dvc_mod);
                        lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(dvc_mod);
                        lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    } 

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_queued_att_duty_is_rcvd_duty(dv)
    requires inv_consensus_instances_only_for_rcvd_duties(dv)  
    ensures inv_consensus_instances_only_for_rcvd_duties(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        assert inv_queued_att_duty_is_rcvd_duty_body(dvc);
                        assert inv_consensus_instances_only_for_rcvd_duties_body(dvc);                                           
                        lem_inv_consensus_instances_only_for_rcvd_duties_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv_consensus_instances_only_for_rcvd_duties_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_consensus_instances_only_for_rcvd_duties_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv_consensus_instances_only_for_rcvd_duties_body(dvc');
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_consensus_instances_only_for_rcvd_duties_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv_consensus_instances_only_for_rcvd_duties_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lem_inv_queued_att_duty_is_rcvd_duty_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_queued_att_duty_is_rcvd_duty_body(dvc_mod);
                        lem_inv_consensus_instances_only_for_rcvd_duties_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_consensus_instances_only_for_rcvd_duties_body(dvc_mod);
                        lem_inv_consensus_instances_only_for_rcvd_duties_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_consensus_instances_only_for_rcvd_duties_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    } 

}   
        