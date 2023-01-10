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
include "invs_fnc_2.dfy"
include "invs_dv_next_1.dfy"
include "invs_dv_next_3.dfy"

module Invs_DV_Next_2
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
    import opened Invs_DV_Next_1
    import opened Fnc_Invs_2
    import opened DVC_Spec_Axioms
    import opened Invs_DV_Next_3

    lemma lem_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_queued_att_duty_is_rcvd_duty(dv)
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty(dv)
    requires inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties(dv)  
    ensures inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties(dv')
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
                        assert inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(dvc);                                           
                        lem_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(dvc');
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lem_inv_queued_att_duty_is_rcvd_duty_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_queued_att_duty_is_rcvd_duty_body(dvc_mod);
                        lem_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(dvc_mod);
                        lem_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }

    lemma lem_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_queued_att_duty_is_rcvd_duty(dv)
    requires inv_consensus_instances_only_for_rcvd_duties(dv)
    requires inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred(dv)  
    ensures inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred(dv')
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
                        assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(dvc);                                           
                        lem_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(dvc');
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lem_inv_queued_att_duty_is_rcvd_duty_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_queued_att_duty_is_rcvd_duty_body(dvc_mod);
                        lem_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(dvc_mod);
                        lem_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }

    lemma lem_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_queued_att_duty_is_rcvd_duty(dv)
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty(dv)
    requires inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k(dv)  
    ensures inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k(dv')
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
                        assert inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(dvc);                                           
                        lem_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(dvc');
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lem_inv_queued_att_duty_is_rcvd_duty_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_queued_att_duty_is_rcvd_duty_body(dvc_mod);
                        lem_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(dvc_mod);
                        lem_inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_validity_pred_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }

    lemma lem_inv_monotonic_att_slashing_db_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    ensures inv_monotonic_att_slashing_db(dv, event, dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        lem_inv_monotonic_att_slashing_db_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv_monotonic_att_slashing_db_body(dvc, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_monotonic_att_slashing_db_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv_monotonic_att_slashing_db_body(dvc, dvc');
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_monotonic_att_slashing_db_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv_monotonic_att_slashing_db_body(dvc, dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lem_inv_monotonic_att_slashing_db_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_monotonic_att_slashing_db_body(dvc, dvc_mod);
                        lem_inv_monotonic_att_slashing_db_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_monotonic_att_slashing_db_body(dvc_mod, dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }

    lemma lem_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_queued_att_duty_is_rcvd_duty(dv)
    requires inv_consensus_instances_only_for_rcvd_duties(dv)
    requires inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db(dv)  
    ensures inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db(dv')
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
                        assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(dvc);                                           
                        lem_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(dvc');
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lem_inv_queued_att_duty_is_rcvd_duty_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_queued_att_duty_is_rcvd_duty_body(dvc_mod);
                        lem_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(dvc_mod);
                        lem_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }


    lemma lem_inv_monotonic_att_slashing_db_hist_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    ensures inv_monotonic_att_slashing_db_hist(dv, event, dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        lem_inv_monotonic_att_slashing_db_hist_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv_monotonic_att_slashing_db_hist_body(dvc, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_monotonic_att_slashing_db_hist_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv_monotonic_att_slashing_db_hist_body(dvc, dvc');
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_monotonic_att_slashing_db_hist_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv_monotonic_att_slashing_db_hist_body(dvc, dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lem_inv_monotonic_att_slashing_db_hist_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_monotonic_att_slashing_db_hist_body(dvc, dvc_mod);
                        lem_inv_monotonic_att_slashing_db_hist_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_monotonic_att_slashing_db_hist_body(dvc_mod, dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }

    

    lemma lem_inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist(dv)
    ensures inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        lem_inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_body(dvc');
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lem_inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_body(dvc_mod);
                        lem_inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }

    lemma lem_inv_construct_signed_attestation_signature_assumptions_helper_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_construct_signed_attestation_signature_assumptions_helper(dv)
    ensures inv_construct_signed_attestation_signature_assumptions_helper(dv')    
    {
        assert dv.construct_signed_attestation_signature == dv'.construct_signed_attestation_signature;
    }

    lemma lem_inv_all_in_transit_messages_were_sent_body_network_spec_next<M>(
        e: Network<M>,
        e': Network<M>,
        n: BLSPubkey,
        messagesToBeSent: set<MessaageWithRecipient<M>>,
        messagesReceived: set<M>
    )
    requires NetworkSpec.Next(e, e', n, messagesToBeSent, messagesReceived)
    requires inv_all_in_transit_messages_were_sent_body(e)
    ensures inv_all_in_transit_messages_were_sent_body(e')
    {}

    

    lemma lem_inv_all_in_transit_messages_were_sent_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_all_in_transit_messages_were_sent(dv)
    ensures inv_all_in_transit_messages_were_sent(dv')    
    {
        var n: BLSPubkey,
            messagesToBeSent: set<MessaageWithRecipient<AttestationShare>>,
            messagesReceived: set<AttestationShare> 
            :|
            NetworkSpec.Next<AttestationShare>(
                dv.att_network, 
                dv'.att_network, 
                n, 
                messagesToBeSent, 
                messagesReceived);

        lem_inv_all_in_transit_messages_were_sent_body_network_spec_next<AttestationShare>(
                dv.att_network, 
                dv'.att_network, 
                n, 
                messagesToBeSent, 
                messagesReceived);  
    }

    lemma lem_inv_all_in_transit_messages_were_sent_invNetwork(dv: DVState)
    requires inv_all_in_transit_messages_were_sent(dv)
    ensures invNetwork(dv)
    {}

    lemma lem_inv_attestation_shares_to_broadcast_are_sent_messages_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )       
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_quorum_constraints(dv)
    requires inv_unchanged_honesty(dv)
    requires inv_only_dv_construct_signed_attestation_signature(dv)
    requires same_honest_nodes_in_dv_and_ci(dv)    
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(dv)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(dv)
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(dv)      
    requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(dv)       
    requires inv_attestation_shares_to_broadcast_are_sent_messages(dv)    
    ensures inv_attestation_shares_to_broadcast_are_sent_messages(dv')
    {   
        lem_inv_quorum_constraints_dv_next(dv, event, dv');
        lem_inv_unchanged_honesty_dv_next(dv, event, dv');
        lem_inv_only_dv_construct_signed_attestation_signature_dv_next(dv, event, dv');

        assert && inv_quorum_constraints(dv')
               && inv_unchanged_honesty(dv')
               && inv_only_dv_construct_signed_attestation_signature(dv');
        

        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                assert && dvc.peers == dvc'.peers
                       && |dvc.peers| > 0 ;

                match nodeEvent
                {
                    case ServeAttstationDuty(att_duty) =>     
                        lem_inv_attestation_shares_to_broadcast_are_sent_messages_f_serve_attestation_duty(dvc, att_duty, dvc');                        
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        var att_network := dv.att_network;
                        var att_network' := dv'.att_network;
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper6(dv, event, dv');
                        lem_inv_attestation_shares_to_broadcast_are_sent_messages_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc', nodeOutputs);   
                        assert      att_network'.allMessagesSent
                                ==  att_network.allMessagesSent + getMessagesFromMessagesWithRecipient(nodeOutputs.att_shares_sent);               
                    
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_attestation_shares_to_broadcast_are_sent_messages_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                                                

                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lem_inv_attestation_shares_to_broadcast_are_sent_messages_add_block_to_bn(dvc, block, dvc_mod);
                        lem_inv_attestation_shares_to_broadcast_are_sent_messages_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                                                
                                                
                    case ResendAttestationShares =>                         
                        lem_inv_attestation_shares_to_broadcast_are_sent_messages_f_resend_attestation_share(dvc, dvc');

                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }        
    }  

    lemma lem_inv39_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )       
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    ensures dv.att_network.allMessagesSent <= dv'.att_network.allMessagesSent
    {}

    lemma lem_inv_rcvd_attn_shares_are_from_sent_messages_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )       
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_all_in_transit_messages_were_sent(dv)
    requires inv_rcvd_attn_shares_are_from_sent_messages(dv)
    ensures inv_rcvd_attn_shares_are_from_sent_messages(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(att_duty) =>     
                        lem_inv_rcvd_attn_shares_are_from_sent_messages_f_serve_attestation_duty(dvc, att_duty, dvc');                        
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_rcvd_attn_shares_are_from_sent_messages_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');                        

                    case ReceivedAttestationShare(attestation_share) =>    
                        assert NetworkSpec.Next(dv.att_network, dv'.att_network, node, nodeOutputs.att_shares_sent, {attestation_share});
                        assert multiset(addReceipientToMessages<AttestationShare>({attestation_share}, node)) <= dv.att_network.messagesInTransit;
                        assert MessaageWithRecipient(message := attestation_share, receipient := node) in dv.att_network.messagesInTransit;        
                        assert attestation_share in dv.att_network.allMessagesSent;
                        assert attestation_share in dv'.att_network.allMessagesSent;
                        
                        lem_inv39_dv_next(dv, event, dv');
                        assert dv.att_network.allMessagesSent <= dv'.att_network.allMessagesSent;
                        
                        lem_inv_rcvd_attn_shares_are_from_sent_messages_f_listen_for_attestation_shares(dvc, attestation_share, dvc');  

                        assert dvc' == f_listen_for_attestation_shares(dvc, attestation_share).state;

                        var k := (attestation_share.data, attestation_share.aggregation_bits);
                        forall i, j | && i in dvc'.rcvd_attestation_shares.Keys 
                                      && j in dvc'.rcvd_attestation_shares[i].Keys
                        ensures dvc'.rcvd_attestation_shares[i][j] <= dv'.att_network.allMessagesSent;
                        {
                            if ( || i != attestation_share.data.slot
                                 || j != k
                               )
                            {             
                                lem_inv_rcvd_attn_shares_are_from_sent_messages_f_listen_for_attestation_shares_domain(
                                    dvc,
                                    attestation_share,
                                    dvc'
                                );
                                assert && i in dvc.rcvd_attestation_shares.Keys 
                                       && j in dvc.rcvd_attestation_shares[i].Keys;
                                assert dvc'.rcvd_attestation_shares[i][j] <= dvc.rcvd_attestation_shares[i][j];                                
                                assert dvc.rcvd_attestation_shares[i][j] <= dv.att_network.allMessagesSent;
                                lemmaSubsetOfSubset(
                                    dvc'.rcvd_attestation_shares[i][j],
                                    dvc.rcvd_attestation_shares[i][j],
                                    dv.att_network.allMessagesSent
                                );
                                assert dv.att_network.allMessagesSent <= dv'.att_network.allMessagesSent;
                                lemmaSubsetOfSubset(
                                    dvc'.rcvd_attestation_shares[i][j],                                    
                                    dv.att_network.allMessagesSent,
                                    dv'.att_network.allMessagesSent
                                );
                                assert dvc'.rcvd_attestation_shares[i][j] <= dv'.att_network.allMessagesSent;
                            }
                            else
                            {
                                if  && i == attestation_share.data.slot
                                    && j == k
                                    && ( || i !in dvc.rcvd_attestation_shares.Keys
                                         || j !in dvc.rcvd_attestation_shares[i].Keys
                                       )                                       
                                {
                                    
                                    assert dvc'.rcvd_attestation_shares[i][j] <= {attestation_share};
                                    
                                    
                                    assert attestation_share in dv'.att_network.allMessagesSent;                                    
                                    lemmaFromMemberToSingletonSet(attestation_share, dv'.att_network.allMessagesSent);
                                    assert {attestation_share} <= dv'.att_network.allMessagesSent;

                                    lemmaSubsetOfSubset(
                                            dvc'.rcvd_attestation_shares[i][j],
                                            {attestation_share},
                                            dv'.att_network.allMessagesSent
                                        );
                                    assert dvc'.rcvd_attestation_shares[i][j] <= dv'.att_network.allMessagesSent;                                     
                                    
                                }
                                else
                                {
                                    assert  && i == attestation_share.data.slot
                                            && j == k
                                            && i in dvc.rcvd_attestation_shares.Keys 
                                            && j in dvc.rcvd_attestation_shares[i].Keys;

                                    
                                    assert dvc'.rcvd_attestation_shares[i][j] 
                                                <= dvc.rcvd_attestation_shares[i][j] + {attestation_share}; 

                                    assert dvc.rcvd_attestation_shares[i][j] 
                                                <= dv.att_network.allMessagesSent;                                                
                                    assert dv.att_network.allMessagesSent <= dv'.att_network.allMessagesSent;      
                                    lemmaSubsetOfSubset(
                                        dvc.rcvd_attestation_shares[i][j],
                                        dv.att_network.allMessagesSent,
                                        dv'.att_network.allMessagesSent);                                    
                                    assert dvc.rcvd_attestation_shares[i][j] 
                                                <= dv'.att_network.allMessagesSent;

                                    assert attestation_share in dv'.att_network.allMessagesSent;                                    
                                    lemmaFromMemberToSingletonSet(attestation_share, dv'.att_network.allMessagesSent);
                                    assert {attestation_share} <= dv'.att_network.allMessagesSent;

                                    lemmaUnionOfSubsets(dvc.rcvd_attestation_shares[i][j], {attestation_share}, dv'.att_network.allMessagesSent);                                    
                                    assert dvc.rcvd_attestation_shares[i][j] + {attestation_share}
                                                <= dv'.att_network.allMessagesSent;

                                    lemmaSubsetOfSubset(
                                        dvc'.rcvd_attestation_shares[i][j],
                                        dvc.rcvd_attestation_shares[i][j] + {attestation_share},
                                        dv'.att_network.allMessagesSent);
                                    
                                    assert dvc'.rcvd_attestation_shares[i][j] <= dv'.att_network.allMessagesSent;                                                                         
                                }
                            }
                        }
                        assert inv_rcvd_attn_shares_are_from_sent_messages(dv');

                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lem_inv_rcvd_attn_shares_are_from_sent_messages_add_block_to_bn(dvc, block, dvc_mod);
                        lem_inv_rcvd_attn_shares_are_from_sent_messages_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                                                
                                                
                    case ResendAttestationShares =>                         
                        lem_inv_rcvd_attn_shares_are_from_sent_messages_f_resend_attestation_share(dvc, dvc');

                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }        
    }  

    lemma lem_inv_available_latest_attestation_duty_is_from_dv_seq_of_att_duties_new_body_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEvent.requires(dv, event, dv')  
    requires NextEvent(dv, event, dv')  
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b(dv)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_c(dv)
    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_c(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];   
                
                assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(
                            dv,
                            node,
                            dvc,
                            dv.index_next_attestation_duty_to_be_served
                );

                assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_new_body(
                            node,
                            dvc,
                            dv.sequence_attestation_duties_to_be_served,
                            dv.index_next_attestation_duty_to_be_served
                );

                assert inv_queued_att_duties_are_from_dv_seq_of_att_duties_body_body(
                            dv,
                            node,
                            dvc,
                            dv.index_next_attestation_duty_to_be_served
                );

                assert inv_available_latest_attestation_duty_is_from_dv_seq_of_att_duties_new_body(
                            node,
                            dvc,
                            dv.sequence_attestation_duties_to_be_served,
                            dv.index_next_attestation_duty_to_be_served
                );
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                           
                        lem_inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_f_serve_attestation_duty(
                            dvc, 
                            attestation_duty, 
                            dvc',
                            node,
                            dv.sequence_attestation_duties_to_be_served,
                            dv.index_next_attestation_duty_to_be_served
                        );
                        assert inv_queued_att_duties_are_from_dv_seq_of_att_duties_body_body(
                                    dv',
                                    node,
                                    dvc',
                                    dv'.index_next_attestation_duty_to_be_served
                        );
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_available_latest_attestation_duty_is_from_dv_seq_of_att_duties_new_body_f_att_consensus_decided(
                            dvc, 
                            id, 
                            decided_attestation_data, 
                            dvc',
                            node,
                            dv.sequence_attestation_duties_to_be_served,
                            dv.index_next_attestation_duty_to_be_served);
                        assert inv_queued_att_duties_are_from_dv_seq_of_att_duties_body_body(
                                    dv',
                                    node,
                                    dvc',
                                    dv'.index_next_attestation_duty_to_be_served
                        );
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_available_latest_attestation_duty_is_from_dv_seq_of_att_duties_new_body_f_listen_for_attestation_shares(
                            dvc, 
                            attestation_share, 
                            dvc',
                            node,
                            dv.sequence_attestation_duties_to_be_served,
                            dv.index_next_attestation_duty_to_be_served);
                        assert inv_queued_att_duties_are_from_dv_seq_of_att_duties_body_body(
                                    dv',
                                    node,
                                    dvc',
                                    dv'.index_next_attestation_duty_to_be_served
                        );
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := add_block_to_bn(dvc, block);
                        lem_inv_available_latest_attestation_duty_is_from_dv_seq_of_att_duties_new_body_add_block_to_bn(
                            dvc, 
                            block, 
                            dvc_mod,
                            node,
                            dv.sequence_attestation_duties_to_be_served,
                            dv.index_next_attestation_duty_to_be_served
                        );
                        assert inv_available_latest_attestation_duty_is_from_dv_seq_of_att_duties_new_body(
                            node,
                            dvc_mod,
                            dv.sequence_attestation_duties_to_be_served,
                            dv.index_next_attestation_duty_to_be_served
                        );
                        lem_inv_available_latest_attestation_duty_is_from_dv_seq_of_att_duties_new_body_f_listen_for_new_imported_blocks(
                            dvc_mod, 
                            block, 
                            dvc',
                            node,
                            dv.sequence_attestation_duties_to_be_served,
                            dv.index_next_attestation_duty_to_be_served
                        );
                        assert inv_queued_att_duties_are_from_dv_seq_of_att_duties_body_body(
                                    dv',
                                    node,
                                    dvc',
                                    dv'.index_next_attestation_duty_to_be_served
                        );

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }   
    }      
}   
        