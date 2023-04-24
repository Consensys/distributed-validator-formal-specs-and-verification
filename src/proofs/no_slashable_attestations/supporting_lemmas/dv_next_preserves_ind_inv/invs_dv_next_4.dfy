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
        i: Slot
    )
    requires |s1| > 0 || s1 != []
    requires s2 == s1[1..]
    requires 0 <= i < |s2|
    ensures s2[i] == s1[i+1]
    {

    }   

    predicate lem_inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_new_precond(s: DVState) 
    {
        && inv_all_honest_nodes_is_a_quorum(s)
        && inv_unchanged_paras_of_consensus_instances(s)
        && inv_only_dv_construct_signed_attestation_signature(s)
        && same_honest_nodes_in_dv_and_ci(s)    
        && inv_in_transit_messages_are_in_allMessagesSent(s)
        && inv_future_decisions_known_by_dvc_are_decisions_of_quorums(s) //
        && inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(s) //
        && inv_data_of_att_shares_are_decided_values(s) //  
        && inv_the_sequence_of_att_duties_is_in_order_of_slots(s) //
        && inv_available_current_att_duty_is_latest_att_duty(s)
        && construct_signed_attestation_signature_assumptions_helper(
            s.construct_signed_attestation_signature,
            s.dv_pubkey,
            s.all_nodes
        )    
        && inv_rcvd_attestation_shares_are_sent_messages(s) 
        && inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(s)
        && inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)      
        && inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(s)    
        && inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db(s)    
        && inv_every_sent_validity_predicate_is_based_on_a_rcvd_att_duty_and_a_slashing_db_for_dv(s)         
    }

    lemma lem_NonServeAttestationDuty_unchanged_vars(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')      
    requires event.HonestNodeTakingStep?
    requires !event.event.ServeAttestationDuty?
    ensures s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;
    ensures s.sequence_attestation_duties_to_be_served == s'.sequence_attestation_duties_to_be_served  
    {

    }    

    lemma lem_inv_future_decisions_known_by_dvc_are_decisions_of_quorums_f_serve_attestation_duty(
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
    requires inv_future_decisions_known_by_dvc_are_decisions_of_quorums_body(dv, n, process)
    ensures inv_future_decisions_known_by_dvc_are_decisions_of_quorums_body(dv, n, s');
    {
        
    }    

    lemma lem_inv_future_decisions_known_by_dvc_are_decisions_of_quorums_f_att_consensus_decided(
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
    requires inv_future_decisions_known_by_dvc_are_decisions_of_quorums_body(dv, n, process)
    ensures inv_future_decisions_known_by_dvc_are_decisions_of_quorums_body(dv, n, s'); 
    {
        
    }  

    lemma lem_inv_future_decisions_known_by_dvc_are_decisions_of_quorums_f_check_for_next_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires s' == f_check_for_next_duty(process, attestation_duty).state  
    requires inv_future_decisions_known_by_dvc_are_decisions_of_quorums_body(dv, n, process)
    ensures inv_future_decisions_known_by_dvc_are_decisions_of_quorums_body(dv, n, s')
    {
           
    } 

    lemma lem_inv_future_decisions_known_by_dvc_are_decisions_of_quorums_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires inv_future_decisions_known_by_dvc_are_decisions_of_quorums_body(dv, n, process)
    requires inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(dv)
    requires inv_data_of_att_shares_are_decided_values(dv)
    requires pred_axiom_is_my_attestation_2(dv, process, block)
    ensures inv_future_decisions_known_by_dvc_are_decisions_of_quorums_body(dv, n, s');
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

    lemma lem_inv_unchanged_decision_Consensus_Next<D(!new, 0)>(
        s: ConsensusInstance,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,        
        s': ConsensusInstance,
        output: Optional<OutCommand>
    )
    requires ConsensusSpec.Next.requires(s, honest_nodes_validity_predicates, s', output)
    requires ConsensusSpec.Next(s, honest_nodes_validity_predicates, s', output)
    requires isConditionForSafetyTrue(s)
    ensures  s.decided_value.isPresent()
                    ==> 
                    ( && s'.decided_value.isPresent()
                      && s.decided_value.safe_get()
                                        == s'.decided_value.safe_get()
                    )
            ;
    {

    }

    lemma lem_inv_unchanged_decision_ConsensusInstanceStep<D(!new, 0)>(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Types.Event,
        nodeOutputs: DVC_Spec.Outputs,
        s': DVState
    )
    requires DV.ConsensusInstanceStep.requires(s, node, nodeEvent, nodeOutputs, s')
    requires DV.ConsensusInstanceStep(s, node, nodeEvent, nodeOutputs, s')
    requires forall slot: Slot | slot in s.consensus_on_attestation_data.Keys  ::
                    isConditionForSafetyTrue(s.consensus_on_attestation_data[slot])
                    ;
    ensures forall slot: Slot | 
                    && slot in s.consensus_on_attestation_data.Keys 
                    && s.consensus_on_attestation_data[slot].decided_value.isPresent()
                    ::                    
                    && s'.consensus_on_attestation_data[slot].decided_value.isPresent()
                    && s.consensus_on_attestation_data[slot].decided_value.safe_get()
                            == s'.consensus_on_attestation_data[slot].decided_value.safe_get()
                    ;
    {

    }

    lemma lem_inv_every_consensus_instance_isConditionForSafetyTrue_dv_next(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )    
    requires NextEvent.requires(dv, event, dv')  
    requires NextEvent(dv, event, dv')  
    requires inv_every_consensus_instance_isConditionForSafetyTrue(dv)
    ensures inv_every_consensus_instance_isConditionForSafetyTrue(dv')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dv.honest_nodes_states[node];
                var dvc' := dv'.honest_nodes_states[node];   
                
                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) =>                           
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        
                    case ReceivedAttestationShare(attestation_share) =>                         
                       
                    case ImportedNewBlock(block) => 
                
                    case ResendAttestationShares =>                                                                      

                    case NoEvent => 
                        
                }
                
            case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                
        }   
    }  

    lemma lem_inv_unchanged_decision_dv(
        s: DVState,
        event: DV.Event,
        s': DVState,
        slot: Slot
    )
    requires NextEventPreCond(s, event) 
    requires NextEvent(s, event, s')   
    requires inv_every_consensus_instance_isConditionForSafetyTrue(s)
    requires && slot in s.consensus_on_attestation_data.Keys 
             && s.consensus_on_attestation_data[slot].decided_value.isPresent()
    ensures  && s'.consensus_on_attestation_data[slot].decided_value.isPresent()
             && s.consensus_on_attestation_data[slot].decided_value.safe_get()
                == 
                s'.consensus_on_attestation_data[slot].decided_value.safe_get()
    {
        
    }

    // TODO
    lemma lem_inv_future_decisions_known_by_dvc_are_decisions_of_quorums_helper_honest(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')     
    requires lem_inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_new_precond(s)  
    requires inv_every_consensus_instance_isConditionForSafetyTrue(s)
    requires event.HonestNodeTakingStep?
    ensures inv_future_decisions_known_by_dvc_are_decisions_of_quorums_body(s', event.node, s'.honest_nodes_states[event.node]); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                
                lem_inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_dv_next(s, event, s');
                lem_inv_data_of_att_shares_are_decided_values_dv_next(s, event, s');

                forall slot | slot in s_node.future_att_consensus_instances_already_decided 
                ensures && s'.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && s_node.future_att_consensus_instances_already_decided[slot] == s'.consensus_on_attestation_data[slot].decided_value.safe_get()
                {
                    assert && s.consensus_on_attestation_data[slot].decided_value.isPresent()
                           && s_node.future_att_consensus_instances_already_decided[slot] == s.consensus_on_attestation_data[slot].decided_value.safe_get()
                           ;
                    calc 
                    {
                        s_node.future_att_consensus_instances_already_decided[slot];
                        ==
                        s.consensus_on_attestation_data[slot].decided_value.safe_get();                        
                        ==
                        { lem_inv_unchanged_decision_dv(s, event, s', slot); }
                        s'.consensus_on_attestation_data[slot].decided_value.safe_get();
                    }
                }

                assert inv_future_decisions_known_by_dvc_are_decisions_of_quorums_body(s', node, s_node);
                assert inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(s');
                assert inv_data_of_att_shares_are_decided_values(s');             

                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lem_ServeAttestationDuty_constraints(s, event, s');
                        lem_inv_future_decisions_known_by_dvc_are_decisions_of_quorums_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_future_decisions_known_by_dvc_are_decisions_of_quorums_body(s', node, s'_node);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        lem_NonServeAttestationDuty_unchanged_vars(s, event, s');
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lem_inv_future_decisions_known_by_dvc_are_decisions_of_quorums_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_future_decisions_known_by_dvc_are_decisions_of_quorums_body(s', node, s'_node);                        
                   
                    case ReceivedAttestationShare(attestation_share) =>
                        lem_NonServeAttestationDuty_unchanged_vars(s, event, s'); 
                        lem_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        assert inv_future_decisions_known_by_dvc_are_decisions_of_quorums_body(s', node, s'_node);  
                        
                    case ImportedNewBlock(block) => 
                        lem_NonServeAttestationDuty_unchanged_vars(s, event, s');
                        var s_node2 := f_add_block_to_bn(s_node, nodeEvent.block);
                        lem_inv_future_decisions_known_by_dvc_are_decisions_of_quorums_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_future_decisions_known_by_dvc_are_decisions_of_quorums_body(s', node, s'_node);                     
                 
                    case ResendAttestationShares => 
                        lem_NonServeAttestationDuty_unchanged_vars(s, event, s');
                        lem_f_resend_attestation_share_constants(s_node, s'_node);
                        assert inv_future_decisions_known_by_dvc_are_decisions_of_quorums_body(s', node, s'_node);  

                    case NoEvent => 
                        lem_NonServeAttestationDuty_unchanged_vars(s, event, s');
                        assert s_node == s'_node; 
                        assert inv_future_decisions_known_by_dvc_are_decisions_of_quorums_body(s', node, s'_node);                          
                }
        }
    }     

    lemma lem_inv_future_decisions_known_by_dvc_are_decisions_of_quorums(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires lem_inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_new_precond(s)
    requires inv_future_decisions_known_by_dvc_are_decisions_of_quorums(s)
    ensures inv_future_decisions_known_by_dvc_are_decisions_of_quorums(s')
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_future_decisions_known_by_dvc_are_decisions_of_quorums_helper_honest(s, event, s');
                   
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_future_decisions_known_by_dvc_are_decisions_of_quorums_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];

                        var n_state := s.honest_nodes_states[hn];
                        var n_state' := s'.honest_nodes_states[hn];
                        forall slot | slot in n_state'.future_att_consensus_instances_already_decided.Keys
                        ensures && s'.consensus_on_attestation_data[slot].decided_value.isPresent()
                                && n_state'.future_att_consensus_instances_already_decided[slot] == s'.consensus_on_attestation_data[slot].decided_value.safe_get()
                        {
                            assert  && s.consensus_on_attestation_data[slot].decided_value.isPresent()
                                    && n_state.future_att_consensus_instances_already_decided[slot] == s.consensus_on_attestation_data[slot].decided_value.safe_get();
                            
                            assert  n_state.future_att_consensus_instances_already_decided[slot]
                                    ==
                                    n_state'.future_att_consensus_instances_already_decided[slot];

                            lem_inv_unchanged_decision_dv(
                                s,
                                event,
                                s',
                                slot
                            );

                            assert  && s'.consensus_on_attestation_data[slot].decided_value.isPresent()
                                    && s'.consensus_on_attestation_data[slot].decided_value.safe_get() == s.consensus_on_attestation_data[slot].decided_value.safe_get();
                        }
                    }
                    else
                    {
                        lem_inv_future_decisions_known_by_dvc_are_decisions_of_quorums_helper_honest(s, event, s');
                    }
                }  
                assert inv_future_decisions_known_by_dvc_are_decisions_of_quorums(s');
                         
            case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_future_decisions_known_by_dvc_are_decisions_of_quorums_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                }  
                assert inv_future_decisions_known_by_dvc_are_decisions_of_quorums(s');
        }
    }  

    lemma lem_inv_slots_in_future_decided_data_are_correct_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state   
    requires inv_slots_in_future_decided_data_are_correct_body(dv, n, process)
    ensures inv_slots_in_future_decided_data_are_correct_body(dv, n, s');
    {
    }   

    lemma lem_inv_slots_in_future_decided_data_are_correct_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        s': DVCState,
        dv': DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires inv_slots_in_future_decided_data_are_correct_body(dv', n, process)
    requires inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(dv')
    requires inv_data_of_att_shares_are_decided_values(dv')
    requires pred_axiom_is_my_attestation_2(dv', process, block)
    ensures inv_slots_in_future_decided_data_are_correct_body(dv', n, s');
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

    lemma lem_inv_slots_in_future_decided_data_are_correct_f_att_consensus_decided(
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
    requires inv_slots_in_future_decided_data_are_correct_body(dv, n, process)
    ensures inv_slots_in_future_decided_data_are_correct_body(dv, n, s'); 
    {

    }           

    lemma lem_inv_slots_in_future_decided_data_are_correct_f_check_for_next_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey
    )
    requires f_check_for_next_duty.requires(process, attestation_duty)
    requires s' == f_check_for_next_duty(process, attestation_duty).state  
    requires inv_slots_in_future_decided_data_are_correct_body(dv, n, process)
    ensures inv_slots_in_future_decided_data_are_correct_body(dv, n, s')
    {
        
    }  

    lemma lem_inv_slots_in_future_decided_data_are_correct_transpose(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCState,
        n: BLSPubkey
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')      
    requires inv_slots_in_future_decided_data_are_correct_body(s, n, s_node)
    ensures inv_slots_in_future_decided_data_are_correct_body(s', n, s_node)    
    {
        
    }      

    lemma lem_inv_slots_in_future_decided_data_are_correct_helper_honest(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')     
    requires inv_slots_in_future_decided_data_are_correct(s)
    requires lem_inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_new_precond(s)  
    requires event.HonestNodeTakingStep?
    ensures inv_slots_in_future_decided_data_are_correct_body(s', event.node, s'.honest_nodes_states[event.node]); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_slots_in_future_decided_data_are_correct_transpose(s, event, s', s_node, node);
                lem_inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_dv_next(s, event, s');
                lem_inv_data_of_att_shares_are_decided_values_dv_next(s, event, s');

                assert inv_slots_in_future_decided_data_are_correct_body(s', node, s_node);
                assert inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att(s');
                assert inv_data_of_att_shares_are_decided_values(s');             
                
                match nodeEvent
                {
                    case ServeAttestationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lem_ServeAttestationDuty_constraints(s, event, s');
                        lem_inv_slots_in_future_decided_data_are_correct_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node
                        );
                        assert inv_slots_in_future_decided_data_are_correct_body(s', node, s'_node);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        lem_NonServeAttestationDuty_unchanged_vars(s, event, s');
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                                    
                        lem_inv_slots_in_future_decided_data_are_correct_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_slots_in_future_decided_data_are_correct_body(s', node, s'_node);                        
               
                   
                    case ReceivedAttestationShare(attestation_share) =>
                        lem_NonServeAttestationDuty_unchanged_vars(s, event, s'); 
                        lem_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        // lem_inv_slots_in_future_decided_data_are_correct_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_slots_in_future_decided_data_are_correct_body(s', node, s'_node);  
                        

                    case ImportedNewBlock(block) => 
                        lem_NonServeAttestationDuty_unchanged_vars(s, event, s');
                        var s_node2 := f_add_block_to_bn(s_node, nodeEvent.block);
                        lem_inv_slots_in_future_decided_data_are_correct_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_slots_in_future_decided_data_are_correct_body(s', node, s'_node);                     
                    
                 
                    case ResendAttestationShares => 
                        lem_NonServeAttestationDuty_unchanged_vars(s, event, s');
                        lem_f_resend_attestation_share_constants(s_node, s'_node);
                        assert inv_slots_in_future_decided_data_are_correct_body(s', node, s'_node);  

                    case NoEvent => 
                        lem_NonServeAttestationDuty_unchanged_vars(s, event, s');
                        assert s_node == s'_node; 
                        assert inv_slots_in_future_decided_data_are_correct_body(s', node, s'_node);                          
                }
        }
    }     

    lemma lem_inv_slots_in_future_decided_data_are_correct(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires lem_inv_exists_an_honest_node_that_sent_an_att_share_for_every_submitted_att_new_precond(s)
    ensures inv_slots_in_future_decided_data_are_correct(s');  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_slots_in_future_decided_data_are_correct_helper_honest(s, event, s');
                   
                forall hn | hn in s'.honest_nodes_states.Keys   
                ensures inv_slots_in_future_decided_data_are_correct_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_inv_slots_in_future_decided_data_are_correct_transpose(s, event, s', s.honest_nodes_states[hn], hn);
                    }
                }  
                assert inv_slots_in_future_decided_data_are_correct(s');
                         
            case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) =>
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_slots_in_future_decided_data_are_correct_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                    lem_inv_slots_in_future_decided_data_are_correct_transpose(s, event, s', s.honest_nodes_states[hn], hn);
                }  
                assert inv_slots_in_future_decided_data_are_correct(s');

        }
    }             

}