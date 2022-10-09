include "../../../common/commons.dfy"
include "../../common/helper_sets_lemmas.dfy"
include "../common/attestation_creation_instrumented.dfy"
include "../../../specs/consensus/consensus.dfy"
include "../../../specs/network/network.dfy"
include "../../../specs/dv/dv_attestation_creation.dfy"
include "inv.dfy"
include "invs_dv_next_1.dfy"
include "invs_dv_next_2.dfy"
include "invs_dv_next_3.dfy"
include "invs_dv_next_4.dfy"
include "invs_dv_next_5.dfy"
include "../common/common_proofs.dfy"
include "../common/dvc_spec_axioms.dfy"


module Invs_DV_Next_6
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Spec
    import opened DV    
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Helper_Sets_Lemmas
    import opened Invs_DV_Next_1
    import opened Invs_DV_Next_2
    import opened Invs_DV_Next_3
    import opened Invs_DV_Next_4
    import opened Common_Proofs
    import opened DVC_Spec_Axioms    
    import opened Invs_DV_Next_5



    predicate inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_body_body_helper(
        process: DVCState,
        attestation_duties_queue: seq<AttestationDuty>
    )
    {
        forall ad | ad in attestation_duties_queue :: ad.slot !in process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
    }    



    lemma lemma_inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_helper_to_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_body_body(process);
    requires is_sequence_attestation_duties_to_be_served_orderd(dv)
    requires inv_g_iii_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_iii_c_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty_body(process)
    requires inv_no_active_consensus_instance_before_receiving_att_duty_body(process)
    requires inv_head_attetation_duty_queue_higher_than_latest_attestation_duty_body_body(process)
    requires lemma_ServeAttstationDuty2_predicate(dv, index_next_attestation_duty_to_be_served + 1, attestation_duty, n)
    {
        var new_attestation_duties_queue := process.attestation_duties_queue + [attestation_duty];

        if !process.latest_attestation_duty.isPresent()
        {
            assert inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_body_body_helper(process, new_attestation_duties_queue);
        }
        else 
        {
            forall ad |
                ad in process.attestation_duties_queue
            ensures ad.slot < attestation_duty.slot;  
            {
                var i: nat :|
                    && i < index_next_attestation_duty_to_be_served
                    && var an := dv.sequence_attestation_duties_to_be_served[i];
                    && an.attestation_duty == ad
                    && an.node == n
                ;       



                assert ad.slot < attestation_duty.slot;  

            }

            if |process.attestation_duties_queue| > 0 
            {
                forall ad | ad in new_attestation_duties_queue
                ensures ad.slot !in process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;
                {
                    if ad in process.attestation_duties_queue
                    {
                        assert  ad.slot !in process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;
                    }
                    else 
                    {
                        assert ad == attestation_duty;
                        assert ad.slot > process.attestation_duties_queue[0].slot;
                        assert  ad.slot !in process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;
                    }
                }
                assert inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_body_body_helper(process, new_attestation_duties_queue);
            }
            else 
            {
                assert inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_body_body_helper(process, new_attestation_duties_queue);
            }
        }

        assert inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_body_body_helper(process, new_attestation_duties_queue);
    } 

    lemma lemma_NextEventPreCond_ServeAttstationDuty(
        s: DVState,
        event: DV.Event
    )
    requires event.HonestNodeTakingStep?
    requires event.event.ServeAttstationDuty?
    requires validEvent(s, event)
    requires inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue(s);
    requires is_sequence_attestation_duties_to_be_served_orderd(s)
    requires pred_4_1_g_iii_b(s)
    requires pred_4_1_g_iii_c(s)
    requires inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty(s)
    requires inv_no_active_consensus_instance_before_receiving_att_duty(s)
    requires inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(s)                
    {
        lemma_inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_helper_to_f_serve_attestation_duty(
            s.honest_nodes_states[event.node],
            event.event.attestation_duty,
            s,
            event.node,
            s.index_next_attestation_duty_to_be_served
        );
        assert f_serve_attestation_duty.requires(s.honest_nodes_states[event.node], event.event.attestation_duty);
        assert f_process_event.requires(add_block_to_bn_with_event(s, event.node, event.event).honest_nodes_states[event.node], event.event);
        assert NextEventPreCond(s, event);
    }


    lemma lemma_NextEventPreCond(
        s: DVState,
        event: DV.Event
    )
    requires event.HonestNodeTakingStep?
    requires validEvent(s, event)
    requires inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue(s);
    requires is_sequence_attestation_duties_to_be_served_orderd(s)
    requires pred_4_1_g_iii_b(s)
    requires pred_4_1_g_iii_c(s)
    requires inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty(s)
    requires inv_no_active_consensus_instance_before_receiving_att_duty(s)
    requires inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(s)   
    ensures  NextEventPreCond(s, event)                
    {
        if event.event.ServeAttstationDuty?
        {
            lemma_NextEventPreCond_ServeAttstationDuty(s, event);
        }
        assert NextEventPreCond(s, event);
    }        


    lemma lemma_NextPreCond(
        s: DVState
    )
    requires inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue(s);
    requires is_sequence_attestation_duties_to_be_served_orderd(s)
    requires pred_4_1_g_iii_b(s)
    requires pred_4_1_g_iii_c(s)
    requires inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_att_duty(s)
    requires inv_no_active_consensus_instance_before_receiving_att_duty(s)
    requires inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(s)   
    ensures  NextPreCond(s)                
    {
        forall event | validEvent(s, event)
        ensures NextEventPreCond(s, event);
        {
            if event.HonestNodeTakingStep?
            {
                lemma_NextEventPreCond(s, event);
            }
        }

    }     
      

    lemma lemma_inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state   
    requires inv_attestation_duty_queue_is_ordered_body_body(process)
    requires is_sequence_attestation_duties_to_be_served_orderd(dv);
    requires inv_g_iii_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires lemma_ServeAttstationDuty2_predicate(dv, index_next_attestation_duty_to_be_served+1, attestation_duty, n)

    ensures inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_body_body(s')
    {
        var new_p := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
        );  

        if process.attestation_duties_queue != []
        {
            assert inv_attestation_duty_queue_is_ordered_body_body(new_p); 
        }
        else 
        {
            assert inv_attestation_duty_queue_is_ordered_body_body(new_p); 
        }        

        lemma_inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_f_check_for_next_queued_duty(new_p, s', dv, n, index_next_attestation_duty_to_be_served); 
    }  

    lemma lemma_inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_f_att_consensus_decided(
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
    requires inv_attestation_duty_queue_is_ordered_body_body(process)
    requires is_sequence_attestation_duties_to_be_served_orderd(dv);
    requires inv_g_iii_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    ensures inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_body_body(s')
    {
        if  || !process.current_attestation_duty.isPresent()
            || id != process.current_attestation_duty.safe_get().slot 
        {
            return;
        }

        var local_current_attestation_duty := process.current_attestation_duty.safe_get();

        var attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);

        var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
        var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
        var attestation_signature_share := rs_sign_attestation(decided_attestation_data, fork_version, attestation_signing_root, process.rs);
        var attestation_with_signature_share := AttestationShare(
                aggregation_bits := get_aggregation_bits(local_current_attestation_duty.validator_index),
                data := decided_attestation_data, 
                signature := attestation_signature_share
            ); 

        var s_mod := 
            process.(
                current_attestation_duty := None,
                attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                attestation_slashing_db := attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    process.attestation_consensus_engine_state,
                    attestation_slashing_db
                )
            );
       

        lemma_inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_f_check_for_next_queued_duty(
            s_mod, 
            s',
            dv,
            n,
            index_next_attestation_duty_to_be_served
        );          
    }        

    lemma lemma_inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_attestation_duty_queue_is_ordered_body_body(process)
    requires is_sequence_attestation_duties_to_be_served_orderd(dv);
    requires inv_g_iii_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    ensures inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_body_body(s')
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var process :=
                process.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );                     

        if process.current_attestation_duty.isPresent() && process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            // Stop(current_attestation_duty.safe_get().slot);
            var decided_attestation_data := att_consensus_instances_already_decided[process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);
            var s_mod := process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    process.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );


            lemma_inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_f_check_for_next_queued_duty(
                s_mod, 
                s',
                dv,
                n,
                index_next_attestation_duty_to_be_served
            );             
           
        }
    }      

    lemma lemma_inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_f_check_for_next_queued_duty(
        process: DVCState,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state  
    requires inv_attestation_duty_queue_is_ordered_body_body(process)
    ensures inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_body_body(s')
    decreases process.attestation_duties_queue
    {
        if  && process.attestation_duties_queue != [] 
            && (
                || process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided
                || !process.current_attestation_duty.isPresent()
            )    
        {
            if process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided.Keys
            {
                var queue_head := process.attestation_duties_queue[0];
                var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, process.future_att_consensus_instances_already_decided[queue_head.slot]);
                var s_mod := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..],
                    future_att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided - {queue_head.slot},
                    attestation_slashing_db := new_attestation_slashing_db,
                    attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                        process.attestation_consensus_engine_state,
                        new_attestation_slashing_db
                    )                        
                );

                lemma_inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_f_check_for_next_queued_duty(s_mod, s', dv, n, index_next_attestation_duty_to_be_served);

            }
            else 
            {    

            }
        } 
        else 
        {
        }             
    } 

    lemma lemma_inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_easy(
        s_node: DVCState,
        s'_node: DVCState
    )
    requires inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_body_body(s_node)
    requires s_node.attestation_duties_queue == s'_node.attestation_duties_queue
    requires s_node.attestation_consensus_engine_state == s'_node.attestation_consensus_engine_state
    ensures inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_body_body(s'_node)       
    {

    }   

    

    lemma lemma_inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_next_honest(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event) 
    requires NextEvent(s, event, s')
    requires inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue(s)
    requires inv_attestation_duty_queue_is_ordered(s)
    requires is_sequence_attestation_duties_to_be_served_orderd(s);
    requires pred_4_1_g_iii_b(s)
    ensures inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue(s');        
    {
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>    
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];               
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lemma_ServeAttstationDuty2(s, event, s');
                        lemma_inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s, 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        );
                        assert inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_body_body(s'_node);


                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        lemma_NonServeAttstationDuty(s, event, s');
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lemma_inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_body_body(s'_node);                        
                        
                 
               
                   
                    case ReceivedAttestationShare(attestation_share) =>
                        lemma_NonServeAttstationDuty(s, event, s'); 
                        lemma_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        assert inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_body_body(s'_node);    
                        

                    case ImportedNewBlock(block) => 
                        lemma_NonServeAttstationDuty(s, event, s');
                        var s_node2 := add_block_to_bn(s_node, nodeEvent.block);
                        lemma_inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_body_body(s'_node);
                                          
                    
                 
                    case ResendAttestationShares => 
                        lemma_NonServeAttstationDuty(s, event, s');
                        lemma_f_resend_attestation_share_constants(s_node, s'_node);

                    case NoEvent => 
                        lemma_NonServeAttstationDuty(s, event, s');
                        assert s_node == s'_node;                         
                }   
                assert inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_body_body(s'_node);    
                assert inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue(s');          


            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) => 
                assert inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue(s'); 

        }
    }


}