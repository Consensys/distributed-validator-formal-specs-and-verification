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
include "invs_dv_next_2.dfy"

module Invs_DV_Next_3
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
    import opened Invs_DV_Next_2

    lemma lem_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
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
                        assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(dvc);   
                        assert inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(dvc);                                           
                        lem_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(dvc');
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := f_add_block_to_bn(dvc, block);
                        lem_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body_f_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(dvc_mod);
                        lem_inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_att_slashing_db_hist_keeps_track_of_only_rcvd_att_duties_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
        }   
    }

    lemma lem_inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_consensus_instances_only_for_rcvd_duties(dv)
    requires inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate(dv)  
    ensures inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        
                        assert inv_consensus_instances_only_for_rcvd_duties_body(dvc);   
                        assert inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate_body(dvc);                                           
                        lem_inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate_body_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate_body_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate_body(dvc');
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate_body_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := f_add_block_to_bn(dvc, block);
                        lem_inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate_body_f_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate_body(dvc_mod);
                        lem_inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate_body_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
        }   
    }

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty(dv)
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k(dv)  
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];                
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>   
                        
                        assert inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_att_duty_body(dvc);   
                        assert inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(dvc);                                           
                        lem_inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(dvc');
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := f_add_block_to_bn(dvc, block);
                        lem_inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body_f_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(dvc_mod);
                        lem_inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_current_validity_predicate_for_slot_k_is_stored_in_att_slashing_db_hist_k_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
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
                        lem_inv_monotonic_att_slashing_db_body_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv_monotonic_att_slashing_db_body(dvc, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_monotonic_att_slashing_db_body_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv_monotonic_att_slashing_db_body(dvc, dvc');
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_monotonic_att_slashing_db_body_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv_monotonic_att_slashing_db_body(dvc, dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := f_add_block_to_bn(dvc, block);
                        lem_inv_monotonic_att_slashing_db_body_f_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_monotonic_att_slashing_db_body(dvc, dvc_mod);
                        lem_inv_monotonic_att_slashing_db_body_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_monotonic_att_slashing_db_body(dvc_mod, dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
        }   
    }

    lemma lem_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')    
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
                        
                        assert inv_consensus_instances_only_for_rcvd_duties_body(dvc);   
                        assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(dvc);                                           
                        lem_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(dvc');
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := f_add_block_to_bn(dvc, block);
                        lem_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body_f_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(dvc_mod);
                        lem_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
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
                        lem_inv_monotonic_att_slashing_db_hist_body_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv_monotonic_att_slashing_db_hist_body(dvc, dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_monotonic_att_slashing_db_hist_body_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv_monotonic_att_slashing_db_hist_body(dvc, dvc');
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_monotonic_att_slashing_db_hist_body_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv_monotonic_att_slashing_db_hist_body(dvc, dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := f_add_block_to_bn(dvc, block);
                        lem_inv_monotonic_att_slashing_db_hist_body_f_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_monotonic_att_slashing_db_hist_body(dvc, dvc_mod);
                        lem_inv_monotonic_att_slashing_db_hist_body_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_monotonic_att_slashing_db_hist_body(dvc_mod, dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
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
                        lem_inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_body_f_serve_attestation_duty(dvc, attestation_duty, dvc');
                        assert inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_body(dvc');
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_body_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc');
                        assert inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_body(dvc');
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_body_f_listen_for_attestation_shares(dvc, attestation_share, dvc');
                        assert inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_body(dvc');
                       
                    case ImportedNewBlock(block) => 
                        var dvc_mod := f_add_block_to_bn(dvc, block);
                        lem_inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_body_f_add_block_to_bn(dvc, block, dvc_mod);
                        assert inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_body(dvc_mod);
                        lem_inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_body_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                        
                        assert inv_active_attn_consensus_instances_are_tracked_in_att_slashing_db_hist_body(dvc');

                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
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
    requires inv_unchanged_paras_of_consensus_instances(dv)
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
        lem_inv_unchanged_paras_of_consensus_instances_dv_next(dv, event, dv');
        lem_inv_only_dv_construct_signed_attestation_signature_dv_next(dv, event, dv');

        assert && inv_quorum_constraints(dv')
               && inv_unchanged_paras_of_consensus_instances(dv')
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
                        if id == decided_attestation_data.slot
                        {
                            lem_inv_attestation_shares_to_broadcast_are_sent_messages_f_att_consensus_decided(dvc, id, decided_attestation_data, dvc', nodeOutputs);   
                            assert att_network'.allMessagesSent
                                        == att_network.allMessagesSent + getMessagesFromMessagesWithRecipient(nodeOutputs.att_shares_sent);               
                        }
                                                
                    case ReceivedAttestationShare(attestation_share) =>                         
                        lem_inv_attestation_shares_to_broadcast_are_sent_messages_f_listen_for_attestation_shares(dvc, attestation_share, dvc');                                                

                    case ImportedNewBlock(block) => 
                        var dvc_mod := f_add_block_to_bn(dvc, block);
                        lem_inv_attestation_shares_to_broadcast_are_sent_messages_add_block_to_bn(dvc, block, dvc_mod);
                        lem_inv_attestation_shares_to_broadcast_are_sent_messages_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                                                
                                                
                    case ResendAttestationShares =>                         
                        lem_inv_attestation_shares_to_broadcast_are_sent_messages_f_resend_attestation_share(dvc, dvc');

                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
        }        
    }  

    // TODO: Rename
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
                        var dvc_mod := f_add_block_to_bn(dvc, block);
                        lem_inv_rcvd_attn_shares_are_from_sent_messages_f_add_block_to_bn(dvc, block, dvc_mod);
                        lem_inv_rcvd_attn_shares_are_from_sent_messages_f_listen_for_new_imported_blocks(dvc_mod, block, dvc');                                                
                                                
                    case ResendAttestationShares =>                         
                        lem_inv_rcvd_attn_shares_are_from_sent_messages_f_resend_attestation_share(dvc, dvc');

                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
        }        
    }  

    lemma lem_inv_available_latest_attestation_duty_is_from_dv_seq_of_att_duties_new_body_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEvent.requires(dv, event, dv')  
    requires NextEvent(dv, event, dv')  
    requires inv_latest_attestation_duty_is_from_dv_seq_of_att_duties(dv)
    ensures inv_latest_attestation_duty_is_from_dv_seq_of_att_duties(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];   
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>                           
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                       
                    case ImportedNewBlock(block) => 
                
                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
        }   
    }      

    lemma lem_inv_rcvd_att_duty_is_from_dv_seq_for_rcvd_att_duty_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_rcvd_att_duty_is_from_dv_seq_for_rcvd_att_duty(dv)
    ensures inv_rcvd_att_duty_is_from_dv_seq_for_rcvd_att_duty(dv')
    {  
        assert pred_unchanged_dvn_seq_of_att_duties(dv, dv');

        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>    
                        assert  dv'.index_next_attestation_duty_to_be_served 
                                ==
                                dv.index_next_attestation_duty_to_be_served + 1;
                        assert  inv_rcvd_att_duty_is_from_dv_seq_for_rcvd_att_duty_body_body(                
                                    attestation_duty, 
                                    node, 
                                    dv'.sequence_attestation_duties_to_be_served,
                                    dv'.index_next_attestation_duty_to_be_served
                                );
                        lem_inv_rcvd_att_duty_is_from_dv_seq_for_rcvd_att_duty_body_f_serve_attestation_duty( 
                                dvc,
                                attestation_duty,                                
                                dvc',
                                node,
                                dv'.sequence_attestation_duties_to_be_served,    
                                dv'.index_next_attestation_duty_to_be_served 
                            );
                        assert inv_rcvd_att_duty_is_from_dv_seq_for_rcvd_att_duty(dv');    

                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_inv_rcvd_att_duty_is_from_dv_seq_for_rcvd_att_duty_body_f_att_consensus_decided(
                                dvc,
                                id,
                                decided_attestation_data,
                                dvc',
                                node,
                                dv'.sequence_attestation_duties_to_be_served,    
                                dv'.index_next_attestation_duty_to_be_served
                            );
                        assert inv_rcvd_att_duty_is_from_dv_seq_for_rcvd_att_duty(dv');    

                    case ReceivedAttestationShare(attestation_share) =>   
                        lem_inv_rcvd_att_duty_is_from_dv_seq_for_rcvd_att_duty_body_f_listen_for_attestation_shares(
                                dvc,
                                attestation_share,
                                dvc',
                                node,
                                dv'.sequence_attestation_duties_to_be_served,    
                                dv'.index_next_attestation_duty_to_be_served
                            );      
                        assert inv_rcvd_att_duty_is_from_dv_seq_for_rcvd_att_duty(dv');                
   
                    case ImportedNewBlock(block) => 
                        var dvc := f_add_block_to_bn(dvc, nodeEvent.block);
                        lem_inv_rcvd_att_duty_is_from_dv_seq_for_rcvd_att_duty_body_f_listen_for_new_imported_blocks(
                            dvc,
                            block,
                            dvc',
                            node,
                            dv'.sequence_attestation_duties_to_be_served,    
                            dv'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_rcvd_att_duty_is_from_dv_seq_for_rcvd_att_duty(dv');
                                          
                    case ResendAttestationShares =>  
                        assert inv_rcvd_att_duty_is_from_dv_seq_for_rcvd_att_duty(dv');                       
                        
                    case NoEvent => 
                        assert inv_rcvd_att_duty_is_from_dv_seq_for_rcvd_att_duty(dv');        
                        
                }

            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                assert inv_rcvd_att_duty_is_from_dv_seq_for_rcvd_att_duty(dv');        
                
        }   
    }  

    

    lemma lem_inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties(dv)
    ensures inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties(dv')
    {  

        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>    
                        lem_inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_body_f_serve_attestation_duty(
                            dvc,
                            attestation_duty,
                            dvc'
                        );
                        assert inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties(dv'); 
                        

                    case AttConsensusDecided(id, decided_attestation_data) => 
                        assert inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties(dv');         

                    case ReceivedAttestationShare(attestation_share) =>   
                        assert inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties(dv');              
   
                    case ImportedNewBlock(block) => 
                        assert inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties(dv');     
                                          
                    case ResendAttestationShares =>  
                        assert inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties(dv');     

                    case NoEvent => 
                        assert dvc == dvc'; 
                        assert dvc.all_rcvd_duties == dvc'.all_rcvd_duties;  
                        assert inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties(dv'); 
                }

            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                assert inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties(dv');        
                
        }   
    }

    lemma lem_inv_no_rcvd_att_duty_is_higher_than_latest_att_duty_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_no_rcvd_att_duty_is_higher_than_latest_att_duty(dv)
    requires inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties(dv)
    ensures inv_no_rcvd_att_duty_is_higher_than_latest_att_duty(dv')
    {  

        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>    
                        lem_inv_no_rcvd_att_duty_is_higher_than_latest_att_duty_body_f_serve_attestation_duty(
                            dvc,
                            attestation_duty,
                            dvc'
                        );
                        assert inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties(dv'); 
                        

                    case AttConsensusDecided(id, decided_attestation_data) => 
                        assert inv_no_rcvd_att_duty_is_higher_than_latest_att_duty(dv');         

                    case ReceivedAttestationShare(attestation_share) =>   
                        assert inv_no_rcvd_att_duty_is_higher_than_latest_att_duty(dv');              
   
                    case ImportedNewBlock(block) => 
                        assert inv_no_rcvd_att_duty_is_higher_than_latest_att_duty(dv');     
                                          
                    case ResendAttestationShares =>  
                        assert inv_no_rcvd_att_duty_is_higher_than_latest_att_duty(dv');     

                    case NoEvent => 
                        assert dvc == dvc'; 
                        assert dvc.all_rcvd_duties == dvc'.all_rcvd_duties;  
                        assert inv_no_rcvd_att_duty_is_higher_than_latest_att_duty(dv'); 
                }

            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                assert inv_no_rcvd_att_duty_is_higher_than_latest_att_duty(dv');        
                
        }   
    }


    lemma lem_inv_unique_rcvd_att_duty_per_slot_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEventPreCond(dv, event)
    requires NextEvent(dv, event, dv')  
    requires inv_unique_rcvd_att_duty_per_slot(dv)
    requires inv_no_rcvd_att_duty_is_higher_than_latest_att_duty(dv)
    requires inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties(dv)
    ensures inv_unique_rcvd_att_duty_per_slot(dv')
    {  

        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) =>    
                        if !dvc.latest_attestation_duty.isPresent()                            
                        {
                            lem_inv_none_latest_att_duty_and_empty_set_of_rcvd_att_duties_dv_next(dv, event, dv');
                            assert dvc'.all_rcvd_duties == {attestation_duty};
                            assert inv_unique_rcvd_att_duty_per_slot(dv');
                        }
                        else
                        {
                            if dvc.latest_attestation_duty.safe_get().slot < attestation_duty.slot
                            {
                                assert attestation_duty !in dvc.all_rcvd_duties;
                                assert inv_unique_rcvd_att_duty_per_slot(dv');     
                            }   
                            else
                            {
                                assert inv_unique_rcvd_att_duty_per_slot(dv');     
                            }                            
                        }
                        

                    case AttConsensusDecided(id, decided_attestation_data) => 
                        assert inv_unique_rcvd_att_duty_per_slot(dv');         

                    case ReceivedAttestationShare(attestation_share) =>   
                        assert inv_unique_rcvd_att_duty_per_slot(dv');              
   
                    case ImportedNewBlock(block) => 
                        assert inv_unique_rcvd_att_duty_per_slot(dv');     
                                          
                    case ResendAttestationShares =>  
                        assert inv_unique_rcvd_att_duty_per_slot(dv');     

                    case NoEvent => 
                        assert dvc == dvc'; 
                        assert dvc.all_rcvd_duties == dvc'.all_rcvd_duties;  
                        assert inv_unique_rcvd_att_duty_per_slot(dv'); 
                }

            case AdeversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                assert inv_unique_rcvd_att_duty_per_slot(dv');        
                
        }   
    }
}   
        