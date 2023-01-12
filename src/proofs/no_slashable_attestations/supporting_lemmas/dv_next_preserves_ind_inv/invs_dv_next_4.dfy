include "../../../../common/commons.dfy"
include "../../common/attestation_creation_instrumented.dfy"
include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_attestation_creation.dfy"
include "../../../../specs/dvc/dvc_attestation_creation.dfy"

include "../../../common/helper_sets_lemmas.dfy"
include "../../../common/helper_pred_fcn.dfy"
include "../../../no_slashable_attestations/common/common_proofs.dfy"
include "../../../no_slashable_attestations/common/dvc_spec_axioms.dfy"

include "invs_dv_next_1.dfy"
include "invs_dv_next_2.dfy"
include "invs_dv_next_3.dfy"

include "../inv.dfy"


module Invs_DV_Next_4
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Spec
    import opened DV    
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Helper_Sets_Lemmas
    import opened Invs_DV_Next_2
    import opened Invs_DV_Next_3
    import opened DVC_Spec_Axioms
    import opened Common_Proofs
    import opened Helper_Pred_Fcn

    lemma  lem_on_first_seq_element_elimination<T>(
        s1: seq<T>,
        s2: seq<T>,
        i: nat
    )
    requires |s1| > 0 || s1 != []
    requires s2 == s1[1..]
    requires 0 <= i < |s2|
    ensures s2[i] == s1[i+1]
    {

    }   

    predicate lem_inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s: DVState) 
    {
        && inv_quorum_constraints(s)
        && inv_unchanged_honesty(s)
        && inv_only_dv_construct_signed_attestation_signature(s)
        && same_honest_nodes_in_dv_and_ci(s)    
        && invNetwork(s)
        && inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv(s) //
        && inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(s) //
        && inv_data_of_att_share_is_decided_value(s) //  
        && is_sequence_attestation_duties_to_be_served_orderd(s) //
        && inv_current_latest_attestation_duty_match(s)
        && construct_signed_attestation_signature_assumptions_helper(
            s.construct_signed_attestation_signature,
            s.dv_pubkey,
            s.all_nodes
        )    
        && pred_rcvd_attestation_shares_is_in_all_messages_sent(s) 
        && inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
        && inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)      
        && inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)    
        && inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(s)    
        && inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db_for_dv(s)         
    }

    lemma lem_NonServeAttstationDuty_unchanged_vars(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')      
    requires event.HonestNodeTakingStep?
    requires !event.event.ServeAttstationDuty?
    ensures s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;
    ensures s.sequence_attestation_duties_to_be_served == s'.sequence_attestation_duties_to_be_served  
    {

    }    

    lemma lem_inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state   
    requires index_next_attestation_duty_to_be_served > 0    
    requires inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(dv, n, process)
    ensures inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(dv, n, s');
    {
        
    }    

    lemma lem_inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(process, id, decided_attestation_data).state
    requires inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(dv, n, process)
    ensures inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(dv, n, s'); 
    {
        
    }  

    lemma lem_inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_f_check_for_next_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires s' == f_check_for_next_duty(process, attestation_duty).state  
    requires inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(dv, n, process)
    ensures inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(dv, n, s')
    {
           
    } 

    lemma lem_inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(dv, n, process)
    requires inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv)
    requires inv_data_of_att_share_is_decided_value(dv)
    requires pred_axiom_is_my_attestation_2(dv, process, block)
    ensures inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(dv, n, s');
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
                f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var process_after_stopping_consensus_instance :=
                f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                process,
                                block
                            );   

        lem_f_listen_for_new_imported_blocks_helper_1(
            dv,
            process_after_stopping_consensus_instance,
            block,
            new_consensus_instances_already_decided
        );                                    
    }      

    lemma lem_f_listen_for_attestation_shares_constants(
        s: DVCState,
        attestation_share: AttestationShare,
        s': DVCState
    )
    requires f_listen_for_attestation_shares.requires(s, attestation_share)
    requires s' == f_listen_for_attestation_shares(s, attestation_share).state    
    ensures s'.attestation_consensus_engine_state == s.attestation_consensus_engine_state
    ensures s'.attestation_consensus_engine_state.att_slashing_db_hist == s.attestation_consensus_engine_state.att_slashing_db_hist
    ensures s'.latest_attestation_duty == s.latest_attestation_duty
    ensures s'.current_attestation_duty == s.current_attestation_duty
    ensures s'.attestation_slashing_db == s.attestation_slashing_db
    ensures s'.future_att_consensus_instances_already_decided == s.future_att_consensus_instances_already_decided
    {

    }

    lemma lem_f_resend_attestation_share_constants(
        s: DVCState,
        s': DVCState
    )
    requires f_resend_attestation_share.requires(s)
    requires s' == f_resend_attestation_share(s).state    
    ensures s'.attestation_consensus_engine_state == s.attestation_consensus_engine_state
    ensures s'.attestation_consensus_engine_state.att_slashing_db_hist == s.attestation_consensus_engine_state.att_slashing_db_hist
    ensures s'.latest_attestation_duty == s.latest_attestation_duty
    ensures s'.current_attestation_duty == s.current_attestation_duty
    ensures s'.attestation_slashing_db == s.attestation_slashing_db
    ensures s'.future_att_consensus_instances_already_decided == s.future_att_consensus_instances_already_decided
    {

    } 

    // TODO
    lemma lem_inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_helper_honest(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')     
    requires lem_inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s)  
    requires event.HonestNodeTakingStep?
    // ensures inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(s', event.node, s'.honest_nodes_states[event.node]); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                
                lem_inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(s, event, s');
                lem_inv_data_of_att_share_is_decided_value(s, event, s');

                forall slot | slot in s_node.future_att_consensus_instances_already_decided 
                ensures && s'.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && s_node.future_att_consensus_instances_already_decided[slot] == s'.consensus_on_attestation_data[slot].decided_value.safe_get()
                {
                    calc 
                    {
                        s_node.future_att_consensus_instances_already_decided[slot];
                        ==
                        s.consensus_on_attestation_data[slot].decided_value.safe_get();
                        ==
                        s'.consensus_on_attestation_data[slot].decided_value.safe_get();
                    }
                }

                // assert inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(s', node, s_node);

                // // assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(s', node, s_node);
                // // assert inv_queued_att_duties_are_from_dv_seq_of_att_duties_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                // // assert inv_g_a_iii_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                // // assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node);
                // // assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                // assert inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');
                // assert inv_data_of_att_share_is_decided_value(s');             
                // // assert inv_g_a_iv_a_body_body(s', node, s_node);
                // // assert is_sequence_attestation_duties_to_be_served_orderd(s');

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        // assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        // lem_ServeAttstationDuty(s, event, s');
                        // lem_inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_f_serve_attestation_duty(
                        //     s_node,
                        //     attestation_duty,
                        //     s'_node,
                        //     s', 
                        //     node,
                        //     s'.index_next_attestation_duty_to_be_served
                        // );
                        // assert inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(s', node, s'_node);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        // lem_NonServeAttstationDuty_unchanged_vars(s, event, s');
                        // assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                                    
                        // lem_inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_f_att_consensus_decided(
                        //     s_node,
                        //     id,
                        //     decided_attestation_data,
                        //     s'_node,
                        //     s', 
                        //     node,
                        //     s.index_next_attestation_duty_to_be_served
                        // ); 
                        // assert inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(s', node, s'_node);                        
               
                   
                    case ReceivedAttestationShare(attestation_share) =>
                        // lem_NonServeAttstationDuty_unchanged_vars(s, event, s'); 
                        // lem_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        // // lem_inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_helper_easy(s', event, s_node, s'_node, node );
                        // assert inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(s', node, s'_node);  
                        

                    case ImportedNewBlock(block) => 
                        // lem_NonServeAttstationDuty_unchanged_vars(s, event, s');
                        // var s_node2 := f_add_block_to_bn(s_node, nodeEvent.block);
                        // lem_inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_f_listen_for_new_imported_blocks(
                        //     s_node2,
                        //     block,
                        //     s'_node,
                        //     s', 
                        //     node,
                        //     s.index_next_attestation_duty_to_be_served
                        // );  
                        // assert inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(s', node, s'_node);                     
                    
                 
                    case ResendAttestationShares => 
                        // lem_NonServeAttstationDuty_unchanged_vars(s, event, s');
                        // lem_f_resend_attestation_share_constants(s_node, s'_node);
                        // // lem_inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_helper_easy(s', event, s_node, s'_node, node );
                        // assert inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(s', node, s'_node);  

                    case NoEvent => 
                        // lem_NonServeAttstationDuty_unchanged_vars(s, event, s');
                        // assert s_node == s'_node; 
                        // // lem_inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_helper_easy(s', event, s_node, s'_node, node );
                        // assert inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(s', node, s'_node);                          
                }
                // assert inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  
        }
    }     

    lemma lem_inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires lem_inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s)
    ensures inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv(s');  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_helper_honest(s, event, s');
                   
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                    }
                }  
                assert inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv(s');
                         
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    // if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                    }
                }  
                assert inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv(s');

        }
    }  

    lemma lem_inv_slot_in_future_decided_data_is_correct_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state   
    requires inv_slot_in_future_decided_data_is_correct_body(dv, n, process)
    ensures inv_slot_in_future_decided_data_is_correct_body(dv, n, s');
    {
    }   

    lemma lem_inv_slot_in_future_decided_data_is_correct_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        s': DVCState,
        dv': DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires inv_slot_in_future_decided_data_is_correct_body(dv', n, process)
    requires inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv')
    requires inv_data_of_att_share_is_decided_value(dv')
    requires pred_axiom_is_my_attestation_2(dv', process, block)
    ensures inv_slot_in_future_decided_data_is_correct_body(dv', n, s');
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var new_process := f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                process,
                                block
                            );   

        lem_f_listen_for_new_imported_blocks_helper_1(
            dv',
            process,
            block,
            new_consensus_instances_already_decided
        );                                        
    }         

    lemma lem_inv_slot_in_future_decided_data_is_correct_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(process, id, decided_attestation_data).state
    requires inv_slot_in_future_decided_data_is_correct_body(dv, n, process)
    ensures inv_slot_in_future_decided_data_is_correct_body(dv, n, s'); 
    {

    }           

    lemma lem_inv_slot_in_future_decided_data_is_correct_f_check_for_next_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires s' == f_check_for_next_duty(process, attestation_duty).state  
    requires inv_slot_in_future_decided_data_is_correct_body(dv, n, process)
    ensures inv_slot_in_future_decided_data_is_correct_body(dv, n, s')
    {
        
    }  

    lemma lem_inv_slot_in_future_decided_data_is_correct_transpose(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCState,
        n: BLSPubkey
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')      
    requires inv_slot_in_future_decided_data_is_correct_body(s, n, s_node)
    ensures inv_slot_in_future_decided_data_is_correct_body(s', n, s_node)    
    {
        
    }      

    // TODO
    lemma lem_inv_slot_in_future_decided_data_is_correct_helper_honest(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')     
    requires inv_slot_in_future_decided_data_is_correct(s)
    requires lem_inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s)  
    requires event.HonestNodeTakingStep?
    ensures inv_slot_in_future_decided_data_is_correct_body(s', event.node, s'.honest_nodes_states[event.node]); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_slot_in_future_decided_data_is_correct_transpose(s, event, s', s_node, node);
                lem_inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(s, event, s');
                lem_inv_data_of_att_share_is_decided_value(s, event, s');

                assert inv_slot_in_future_decided_data_is_correct_body(s', node, s_node);
                assert inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');
                assert inv_data_of_att_share_is_decided_value(s');             
                
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lem_ServeAttstationDuty(s, event, s');
                        lem_inv_slot_in_future_decided_data_is_correct_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node
                        );
                        assert inv_slot_in_future_decided_data_is_correct_body(s', node, s'_node);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        lem_NonServeAttstationDuty_unchanged_vars(s, event, s');
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                                    
                        lem_inv_slot_in_future_decided_data_is_correct_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_slot_in_future_decided_data_is_correct_body(s', node, s'_node);                        
               
                   
                    case ReceivedAttestationShare(attestation_share) =>
                        lem_NonServeAttstationDuty_unchanged_vars(s, event, s'); 
                        lem_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        // lem_inv_slot_in_future_decided_data_is_correct_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_slot_in_future_decided_data_is_correct_body(s', node, s'_node);  
                        

                    case ImportedNewBlock(block) => 
                        lem_NonServeAttstationDuty_unchanged_vars(s, event, s');
                        var s_node2 := f_add_block_to_bn(s_node, nodeEvent.block);
                        lem_inv_slot_in_future_decided_data_is_correct_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_slot_in_future_decided_data_is_correct_body(s', node, s'_node);                     
                    
                 
                    case ResendAttestationShares => 
                        lem_NonServeAttstationDuty_unchanged_vars(s, event, s');
                        lem_f_resend_attestation_share_constants(s_node, s'_node);
                        assert inv_slot_in_future_decided_data_is_correct_body(s', node, s'_node);  

                    case NoEvent => 
                        lem_NonServeAttstationDuty_unchanged_vars(s, event, s');
                        assert s_node == s'_node; 
                        assert inv_slot_in_future_decided_data_is_correct_body(s', node, s'_node);                          
                }
        }
    }     

    lemma lem_inv_slot_in_future_decided_data_is_correct(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires lem_inv_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s)
    ensures inv_slot_in_future_decided_data_is_correct(s');  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_slot_in_future_decided_data_is_correct_helper_honest(s, event, s');
                   
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_slot_in_future_decided_data_is_correct_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_inv_slot_in_future_decided_data_is_correct_transpose(s, event, s', s.honest_nodes_states[hn], hn);
                    }
                }  
                assert inv_slot_in_future_decided_data_is_correct(s');
                         
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_slot_in_future_decided_data_is_correct_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                    lem_inv_slot_in_future_decided_data_is_correct_transpose(s, event, s', s.honest_nodes_states[hn], hn);
                }  
                assert inv_slot_in_future_decided_data_is_correct(s');

        }
    }             

}