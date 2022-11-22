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
    import opened Invs_DV_Next_3
    import opened DVC_Spec_Axioms
    import opened Common_Proofs
    import opened Helper_Pred_Fcn

    lemma lem_inv_attestation_duty_queue_is_ordered_3_body_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState,
        i: nat, 
        k: nat,
        l: nat, 
        t: nat        
    )
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, n_state)
    requires inv_attestation_duty_queue_is_ordered_3_body_body_premise(dv, n, n_state, i, k, l, t)
    ensures n_state.attestation_duties_queue[i-1].slot == dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot
    {

    }

    lemma lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState,
        n'_state: DVCState
    )
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n , n_state)
    requires n_state.attestation_duties_queue == n'_state.attestation_duties_queue
    ensures inv_attestation_duty_queue_is_ordered_3_body_body(dv, n , n'_state)
    {
        forall i: nat, k, l, t  |
            inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                dv,
                n, 
                n'_state,
                i,
                k, 
                l, 
                t
            )
        ensures 
            n'_state.attestation_duties_queue[i-1].slot == dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot      
        {
            // assert process.attestation_duties_queue != [];
            assert i > 0;

            assert inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                dv,
                n, 
                n_state,
                i,
                k, 
                l, 
                t                        
            );
        }        
    }

    lemma lemma2_inv_attestation_duty_queue_is_ordered_4_body_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState,
        n'_state: DVCState,
        index_next_attestation_duty_to_be_served: nat
    )
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dv, n , n_state, index_next_attestation_duty_to_be_served)
    requires n_state.attestation_duties_queue == n'_state.attestation_duties_queue
    ensures inv_attestation_duty_queue_is_ordered_4_body_body(dv, n , n'_state, index_next_attestation_duty_to_be_served)
    {
        if |n_state.attestation_duties_queue| > 0
        {
            forall i: nat|
                inv_attestation_duty_queue_is_ordered_4_body_body_premise(
                    dv,
                    n, 
                    n'_state,
                    i,
                    index_next_attestation_duty_to_be_served
                )
            ensures 
                var last := n_state.attestation_duties_queue[|n_state.attestation_duties_queue|-1];
                last.slot == dv.sequence_attestation_duties_to_be_served[i].attestation_duty.slot         
        
            {

                assert inv_attestation_duty_queue_is_ordered_4_body_body_premise(
                    dv,
                    n, 
                    n_state,
                    i,
                    index_next_attestation_duty_to_be_served                     
                );
            }  
        }
      
    }    

    lemma lemma3_inv_attestation_duty_queue_is_ordered_3_body_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState,
        n'_state: DVCState
    )
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n , n_state)
    requires |n_state.attestation_duties_queue| > 0
    requires  n'_state.attestation_duties_queue == n_state.attestation_duties_queue[1..]
    ensures inv_attestation_duty_queue_is_ordered_3_body_body(dv, n , n'_state)
    {
        forall i: nat, k, l, t  |
            inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                dv,
                n, 
                n'_state,
                i,
                k, 
                l, 
                t
            )
        ensures 
            n'_state.attestation_duties_queue[i-1].slot == dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot      
        {
            assert n_state.attestation_duties_queue != [];
            assert i > 0;
            lem_on_first_seq_element_elimination(n_state.attestation_duties_queue, n'_state.attestation_duties_queue, i);
            // assert i - 1 >= 0;
            lem_on_first_seq_element_elimination(n_state.attestation_duties_queue, n'_state.attestation_duties_queue, i-1);
            // assert s_mod.attestation_duties_queue[i-1] == process.attestation_duties_queue[i]; 
            assert inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                dv,
                n, 
                n_state,
                i+1,
                k, 
                l, 
                t                        
            );
        }         
    }

    lemma lemma3_inv_attestation_duty_queue_is_ordered_4_body_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState,
        n'_state: DVCState,
        index_next_attestation_duty_to_be_served: nat
    )
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dv, n , n_state, index_next_attestation_duty_to_be_served)
    requires |n_state.attestation_duties_queue| > 0
    requires  n'_state.attestation_duties_queue == n_state.attestation_duties_queue[1..]
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dv, n , n_state, index_next_attestation_duty_to_be_served)
    {
        if |n'_state.attestation_duties_queue| > 0
        {
            forall i: nat  |
                inv_attestation_duty_queue_is_ordered_4_body_body_premise(
                    dv,
                    n, 
                    n'_state,
                    i,
                    index_next_attestation_duty_to_be_served
                )
            ensures 
                var last := n_state.attestation_duties_queue[|n_state.attestation_duties_queue|-1];
                    last.slot == dv.sequence_attestation_duties_to_be_served[i].attestation_duty.slot 
            {
                assert inv_attestation_duty_queue_is_ordered_4_body_body_premise(
                    dv,
                    n, 
                    n_state,
                    i,
                    index_next_attestation_duty_to_be_served                     
                );
            }    
        }
    }


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


    lemma lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_f_serve_attestation_duty(
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
    requires inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, process)
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, process)
    requires inv_g_a_iii_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_g_d_a_body_body(dv, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process) 
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)  
    requires is_sequence_attestation_duties_to_be_served_orderd(dv);
    requires lem_ServeAttstationDuty2_predicate(dv, index_next_attestation_duty_to_be_served, attestation_duty, n)
    ensures inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, s');
    {
        var new_p := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
        );

        if |process.attestation_duties_queue| == 0 
        {
            assert inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, new_p);  
        }
        else 
        {
            forall i: nat, k, l, t  |
                inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                    dv,
                    n, 
                    new_p,
                    i,
                    k, 
                    l, 
                    t
                )
            ensures 
                new_p.attestation_duties_queue[i-1].slot == dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot      
            {
                // assert process.attestation_duties_queue != [];
                assert i > 0;


                if i != |new_p.attestation_duties_queue| - 1
                {
                    assert inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                        dv,
                        n, 
                        process,
                        i,
                        k, 
                        l, 
                        t                        
                    );
                }
                else 
                {
                    assert new_p.attestation_duties_queue[i-1] == process.attestation_duties_queue[|process.attestation_duties_queue|-1];

                    assert l == index_next_attestation_duty_to_be_served-1;

                    assert new_p.attestation_duties_queue[i-1].slot <= dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;

                    assert inv_attestation_duty_queue_is_ordered_4_body_body_premise(dv, n, process, t, index_next_attestation_duty_to_be_served-1);

                    assert new_p.attestation_duties_queue[i-1].slot == dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;
                }

            }   
        }



        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_f_check_for_next_queued_duty(new_p, s', dv, n, index_next_attestation_duty_to_be_served);
    }

    lemma lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_f_att_consensus_decided(
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
    requires inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, process)
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, process)
    requires inv_g_a_iv_a_body_body(dv, n, process)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dv, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process)   
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)

    requires dv.consensus_on_attestation_data[id].decided_value.isPresent()
    requires dv.consensus_on_attestation_data[id].decided_value.safe_get() ==  decided_attestation_data 
    ensures inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, s'); 
    {     
        if  && process.current_attestation_duty.isPresent()
            && id == process.current_attestation_duty.safe_get().slot
        {
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

            assert s_mod.attestation_duties_queue == process.attestation_duties_queue;

            lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process, s_mod);

            assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, s_mod);

            assert get_upperlimit_decided_instances(s_mod) == process.latest_attestation_duty.safe_get().slot + 1;

            if
                &&  |s_mod.attestation_duties_queue| > 0 
                &&   !s_mod.current_attestation_duty.isPresent()        
            {
                forall an |
                    && an in dv.sequence_attestation_duties_to_be_served.Values 
                    && an.node == n 
                    && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot   
                ensures      
                        var slot := an.attestation_duty.slot;
                            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                        
                {
                    var slot := an.attestation_duty.slot;

                    if slot > s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                    
                    }
                    else if slot == s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                         
                    }
                    else 
                    {
                        assert slot < s_mod.latest_attestation_duty.safe_get().slot;
                        assert 
                            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                           
                    }

                }
            }
            assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, s_mod);


            lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_f_check_for_next_queued_duty(s_mod, s', dv, n, index_next_attestation_duty_to_be_served);  
        }           
    }  

    lemma lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        s': DVCState,
        dv': DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv', n, process)
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv', n, process)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv', n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dv', n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv', n, process) 
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)
    requires concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv')
    requires pred_data_of_att_share_is_decided_value(dv')
    requires inv_g_a_iv_a_body_body(dv', n, process)
    requires pred_axiom_is_my_attestation_2(dv', process, block)
    ensures inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv', n, s');
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var new_process :=
                process.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );                     

        if new_process.current_attestation_duty.isPresent() && new_process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            // Stop(current_attestation_duty.safe_get().slot);
            var decided_attestation_data := att_consensus_instances_already_decided[new_process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(new_process.attestation_slashing_db, decided_attestation_data);
            var s_mod := new_process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    new_process.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );

            lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dv', n, process, s_mod);


            lem_f_listen_for_new_imported_blocks_helper_1(
                dv',
                process,
                block,
                new_consensus_instances_already_decided
            );

            assert 
                && dv'.consensus_on_attestation_data[new_process.current_attestation_duty.safe_get().slot].decided_value.isPresent()
                && dv'.consensus_on_attestation_data[new_process.current_attestation_duty.safe_get().slot].decided_value.safe_get() == decided_attestation_data
            ;                        

            assert inv_g_d_a_body_body(dv', n, s_mod);                  

            assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv', n, s_mod);


            if
                &&  |s_mod.attestation_duties_queue| > 0 
                &&   !s_mod.current_attestation_duty.isPresent()        
            {
                forall an |
                    && an in dv'.sequence_attestation_duties_to_be_served.Values 
                    && an.node == n 
                    && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot   
                ensures      
                        var slot := an.attestation_duty.slot;
                            && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                        
                {
                    var slot := an.attestation_duty.slot;

                    if slot > s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                    
                    }
                    else if slot == s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                         
                    }
                    else 
                    {
                        assert slot < s_mod.latest_attestation_duty.safe_get().slot;
                        assert 
                            && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                           
                    }

                }
            }
            assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv', n, s_mod);                 

            
            lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_f_check_for_next_queued_duty(s_mod, s', dv', n, index_next_attestation_duty_to_be_served);                    
        }        
    }           
    
    
    // lemma lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_f_check_for_next_queued_duty_fake(
    //     process: DVCState,
    //     s': DVCState,
    //     dv: DVState,
    //     n: BLSPubkey,
    //     index_next_attestation_duty_to_be_served: nat
    // )
    // requires f_check_for_next_queued_duty.requires(process)
    // requires s' == f_check_for_next_queued_duty(process).state   
    // requires inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, process)
    // requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, process)
    // requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    // // requires inv_g_d_a_body_body(dv, n, process)
    // requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process)  

    // ensures inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, s');
    // decreases process.attestation_duties_queue    
    

    

    lemma lem_inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(
        process: DVCState,        
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat,
        s_mod: DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, process)    
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dv, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process)  
    requires first_queued_att_duty_was_decided_or_ready_to_be_served(process)
    requires first_queued_att_duty_was_decided(process)
    requires s_mod == f_dequeue_attestation_duties_queue(process)
    ensures ( && |s_mod.attestation_duties_queue| > 0 
              && !s_mod.current_attestation_duty.isPresent() )
                    ==> inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, s_mod)
    {
        if  && |s_mod.attestation_duties_queue| > 0 
              && !s_mod.current_attestation_duty.isPresent()
        {
            forall an |
                && an in dv.sequence_attestation_duties_to_be_served.Values 
                && an.node == n 
                && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot
            ensures 
                var slot := an.attestation_duty.slot;
                && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
            ;                          
            {
                var slot := an.attestation_duty.slot;
            
                if an.attestation_duty.slot < process.attestation_duties_queue[0].slot  
                {
                    assert 
                        && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                    ;
                }
                else 
                {
                    var t :|  dv.sequence_attestation_duties_to_be_served[t] == an;
                    assert process.attestation_duties_queue[0] in process.attestation_duties_queue;
                    var k :|  
                            && dv.sequence_attestation_duties_to_be_served[k].node == n 
                            && dv.sequence_attestation_duties_to_be_served[k].attestation_duty == process.attestation_duties_queue[0];
                    assert process.attestation_duties_queue[1] in process.attestation_duties_queue;
                    var l :|  
                            && dv.sequence_attestation_duties_to_be_served[l].node == n 
                            && dv.sequence_attestation_duties_to_be_served[l].attestation_duty == process.attestation_duties_queue[1];   

                    lem_inv_attestation_duty_queue_is_ordered_3_body_body(
                        dv,
                        n,
                        process,
                        1,
                        k,
                        l,
                        t
                    ); 

                
                    assert 
                        && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                    ;
                    
                }
            }
        }
    }

    lemma lem_inv_attestation_duty_queue_is_ordered_3_body_body_f_dequeue_attestation_duties_queue(
        process: DVCState,        
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat,
        s_mod: DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, process)    
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dv, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process)  
    requires first_queued_att_duty_was_decided_or_ready_to_be_served(process)
    requires first_queued_att_duty_was_decided(process)
    requires s_mod == f_dequeue_attestation_duties_queue(process)
    ensures inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, s_mod)   
    {
        forall i: nat, k, l, t  |
                    inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                        dv,
                        n, 
                        s_mod,
                        i,
                        k, 
                        l, 
                        t
                    )
                ensures 
                    s_mod.attestation_duties_queue[i-1].slot == dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot      
                {
                    assert process.attestation_duties_queue != [];
                    assert i > 0;
                    lem_on_first_seq_element_elimination(process.attestation_duties_queue, s_mod.attestation_duties_queue, i);
                    // assert i - 1 >= 0;
                    lem_on_first_seq_element_elimination(process.attestation_duties_queue, s_mod.attestation_duties_queue, i-1);
                    // assert s_mod.attestation_duties_queue[i-1] == process.attestation_duties_queue[i]; 
                    assert inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                        dv,
                        n, 
                        process,
                        i+1,
                        k, 
                        l, 
                        t                        
                    );
                } 

        assert inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, s_mod);
    }

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body_f_dequeue_attestation_duties_queue_helper2(
        process: DVCState,        
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat,
        s_mod: DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)    
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, process)    
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dv, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process)  
    requires first_queued_att_duty_was_decided_or_ready_to_be_served(process)
    requires first_queued_att_duty_was_decided(process)
    requires s_mod == f_dequeue_attestation_duties_queue(process)
    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, s_mod, index_next_attestation_duty_to_be_served)
    {
        forall ad  |
                    && ad in s_mod.attestation_duties_queue
                ensures ad in process.attestation_duties_queue
                {
                    var i :| 0 <= i < |s_mod.attestation_duties_queue|
                                && s_mod.attestation_duties_queue[i] == ad;
                    assert ad in process.attestation_duties_queue;
                }

        assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, s_mod, index_next_attestation_duty_to_be_served);
    } 

    lemma lem_f_check_for_next_queued_duty_helper(
        process: DVCState,        
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat,
        s_mod: DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, process)    
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dv, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process)  
    requires first_queued_att_duty_was_decided_or_ready_to_be_served(process)
    requires first_queued_att_duty_was_decided(process)
    requires s_mod == f_dequeue_attestation_duties_queue(process)
    ensures ( && |s_mod.attestation_duties_queue| > 0 
              && !s_mod.current_attestation_duty.isPresent() )
                    ==> inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, s_mod)
    ensures inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, s_mod)
    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, s_mod, index_next_attestation_duty_to_be_served)
    {
        lem_inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(
            process,
            dv,
            n,
            index_next_attestation_duty_to_be_served,
            s_mod
        );   

        lem_inv_attestation_duty_queue_is_ordered_3_body_body_f_dequeue_attestation_duties_queue(
                process,
                dv,
                n,
                index_next_attestation_duty_to_be_served,
                s_mod
        );  

        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body_f_dequeue_attestation_duties_queue_helper2(
                process,
                dv,
                n,
                index_next_attestation_duty_to_be_served,
                s_mod
        );     
    }

    lemma lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_f_check_for_next_queued_duty(
        process: DVCState,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state   
    requires inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, process)
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, process)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dv, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process)  

    ensures inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, s');
    decreases process.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(process)
        {
            if first_queued_att_duty_was_decided(process)
            {
                var s_mod := f_dequeue_attestation_duties_queue(process);

                lem_f_check_for_next_queued_duty_helper(
                    process,
                    dv,
                    n,
                    index_next_attestation_duty_to_be_served,
                    s_mod
                );                                                                          

                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_f_check_for_next_queued_duty(s_mod, s', dv, n , index_next_attestation_duty_to_be_served);
            }
            else 
            {
                var new_process := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..]
                );   

                var queue_head := process.attestation_duties_queue[0];       

                assert get_upperlimit_decided_instances(s') == s'.latest_attestation_duty.safe_get().slot;

                if process.latest_attestation_duty.isPresent()
                {
                    assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, s');
                }
                else 
                {
                    assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, s');
                }

                
            }
        } 
        else 
        {
            assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, s');
        }       
    }    

    lemma lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_1(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCState,
        n: BLSPubkey
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')      
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(s, n, s_node)
    requires invNetwork(s)
    requires inv_quorum_constraints(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_queued_att_duty_is_rcvd_duty3(s)  
    ensures inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(s', n, s_node)        
    {
        assert s'.index_next_attestation_duty_to_be_served <= s'.index_next_attestation_duty_to_be_served <= s'.index_next_attestation_duty_to_be_served + 1;

        if 
            &&  |s_node.attestation_duties_queue| > 0 
            &&   !s_node.current_attestation_duty.isPresent()   
        {
            forall an |
                && an in s'.sequence_attestation_duties_to_be_served.Values 
                && an.node == n 
                && an.attestation_duty.slot < s_node.attestation_duties_queue[0].slot
            ensures 
                var slot := an.attestation_duty.slot;
                && s'.consensus_on_attestation_data[slot].decided_value.isPresent()
                && construct_SlashingDBAttestation_from_att_data(s'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_node.attestation_slashing_db                
            {
                var slot := an.attestation_duty.slot;
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper2(s, event, s', slot);

                assert
                    && s.consensus_on_attestation_data[slot].decided_value.isPresent()
                    && construct_SlashingDBAttestation_from_att_data(s.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_node.attestation_slashing_db
                    ;                        

                assert
                    && s'.consensus_on_attestation_data[slot].decided_value.isPresent();
                assert
                    && construct_SlashingDBAttestation_from_att_data(s'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_node.attestation_slashing_db
                    ;                      

            }            
        }     
        
    }    

    lemma lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_2(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCState,
        n: BLSPubkey
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')      
    requires inv_g_a_iii_body_body(s, n, s_node, s.index_next_attestation_duty_to_be_served)
    requires invNetwork(s)
    requires inv_quorum_constraints(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_queued_att_duty_is_rcvd_duty3(s)  
    ensures inv_g_a_iii_body_body(s', n, s_node, s.index_next_attestation_duty_to_be_served)        
    {
        assert s'.index_next_attestation_duty_to_be_served <= s'.index_next_attestation_duty_to_be_served <= s'.index_next_attestation_duty_to_be_served + 1;

        assert s.sequence_attestation_duties_to_be_served == s'.sequence_attestation_duties_to_be_served;

        if 
            &&  |s_node.attestation_duties_queue| == 0 
            &&   !s_node.current_attestation_duty.isPresent()   
        {
            forall i:nat  |
                && i < s.index_next_attestation_duty_to_be_served
                && var an := s'.sequence_attestation_duties_to_be_served[i];
                && an.node == n 
            ensures 
                && var an := s'.sequence_attestation_duties_to_be_served[i];
                var slot := an.attestation_duty.slot;
                && s'.consensus_on_attestation_data[slot].decided_value.isPresent()
                && construct_SlashingDBAttestation_from_att_data(s'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_node.attestation_slashing_db            
            {
                var an := s'.sequence_attestation_duties_to_be_served[i];
                var slot := an.attestation_duty.slot;
                assert && s.consensus_on_attestation_data[slot].decided_value.isPresent();
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper2(s, event, s', slot);

                assert
                    && s.consensus_on_attestation_data[slot].decided_value.isPresent()
                    && construct_SlashingDBAttestation_from_att_data(s.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_node.attestation_slashing_db
                    ;                        

                assert
                    && s'.consensus_on_attestation_data[slot].decided_value.isPresent();
                assert
                    && construct_SlashingDBAttestation_from_att_data(s'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_node.attestation_slashing_db
                    ;                      

            }            
        }     
        
    }         

    lemma lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_3(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCState,
        n: BLSPubkey
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')      
    requires inv_attestation_duty_queue_is_ordered_3_body_body(s, n, s_node)
    requires inv_attestation_duty_queue_is_ordered_4_body_body(s, n, s_node, s.index_next_attestation_duty_to_be_served)    

    ensures inv_attestation_duty_queue_is_ordered_3_body_body(s', n, s_node)    
    ensures inv_attestation_duty_queue_is_ordered_4_body_body(s', n, s_node, s.index_next_attestation_duty_to_be_served)    
     
    {

        assert s.sequence_attestation_duties_to_be_served == s'.sequence_attestation_duties_to_be_served;

        forall i, k, l, t  |
            inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                s',
                n, 
                s_node,
                i,
                k, 
                l, 
                t
            )
        ensures
            s_node.attestation_duties_queue[i-1].slot == s'.sequence_attestation_duties_to_be_served[t].attestation_duty.slot     
        {
            assert
            inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                s,
                n, 
                s_node,
                i,
                k, 
                l, 
                t
            );

        }  

        if |s_node.attestation_duties_queue| > 0
        {
            forall i |
                inv_attestation_duty_queue_is_ordered_4_body_body_premise(
                    s',
                    n, 
                    s_node,
                    i,
                    s.index_next_attestation_duty_to_be_served
                )
            ensures
                var last := s_node.attestation_duties_queue[|s_node.attestation_duties_queue|-1];
                last.slot == s'.sequence_attestation_duties_to_be_served[i].attestation_duty.slot
            {
                assert
                inv_attestation_duty_queue_is_ordered_4_body_body_premise(
                    s,
                    n, 
                    s_node,
                    i,
                    s.index_next_attestation_duty_to_be_served
                )
                ;
            }
        } 
     
    }      

    lemma lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_4(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCState,
        n: BLSPubkey
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')      
    requires inv_g_a_iv_a_body_body(s, n, s_node)
    requires invNetwork(s)
    requires inv_quorum_constraints(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_queued_att_duty_is_rcvd_duty3(s)  
    ensures inv_g_a_iv_a_body_body(s', n, s_node)        
    {
        assert s'.index_next_attestation_duty_to_be_served <= s'.index_next_attestation_duty_to_be_served <= s'.index_next_attestation_duty_to_be_served + 1;

        assert s.sequence_attestation_duties_to_be_served == s'.sequence_attestation_duties_to_be_served;

        if 
            &&  |s_node.attestation_duties_queue| > 0 
            &&   s_node.latest_attestation_duty.isPresent()
        {
            forall an |
                && an in s'.sequence_attestation_duties_to_be_served.Values 
                && an.node == n 
                && s_node.latest_attestation_duty.safe_get().slot < an.attestation_duty.slot < s_node.attestation_duties_queue[0].slot
            ensures 
                var slot := an.attestation_duty.slot;
                && s'.consensus_on_attestation_data[slot].decided_value.isPresent()
                && construct_SlashingDBAttestation_from_att_data(s'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_node.attestation_slashing_db          
            {
                var slot := an.attestation_duty.slot;

                assert && s.consensus_on_attestation_data[slot].decided_value.isPresent();
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper2(s, event, s', slot);

                assert
                    && s.consensus_on_attestation_data[slot].decided_value.isPresent()
                    && construct_SlashingDBAttestation_from_att_data(s.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_node.attestation_slashing_db
                    ;                        

                assert
                    && s'.consensus_on_attestation_data[slot].decided_value.isPresent();
                assert
                    && construct_SlashingDBAttestation_from_att_data(s'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_node.attestation_slashing_db
                    ;                      

            }            
        }     
        
    }            

    lemma lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_multiple(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCState,
        n: BLSPubkey
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')      
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s, n, s_node, s.index_next_attestation_duty_to_be_served)
    // requires inv_attestation_duty_queue_is_ordered_3_body_body(s, n, s_node)
    // requires inv_attestation_duty_queue_is_ordered_4_body_body(s, n, s_node, s.index_next_attestation_duty_to_be_served)

    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', n, s_node, s.index_next_attestation_duty_to_be_served)
    // ensures inv_attestation_duty_queue_is_ordered_3_body_body(s', n, s_node)
    // ensures inv_attestation_duty_queue_is_ordered_4_body_body(s', n, s_node, s.index_next_attestation_duty_to_be_served)
    {
        assert s'.index_next_attestation_duty_to_be_served <= s'.index_next_attestation_duty_to_be_served <= s'.index_next_attestation_duty_to_be_served + 1;
        
    }   

    lemma lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_easy(
        s: DVState,
        event: DV.Event,
        s_node: DVCState,
        s'_node: DVCState,
        n: BLSPubkey
    )
    requires inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s, n, s_node)
    requires s_node.latest_attestation_duty == s'_node.latest_attestation_duty
    requires s_node.current_attestation_duty == s'_node.current_attestation_duty
    requires s_node.attestation_slashing_db <= s'_node.attestation_slashing_db
    ensures inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s, n, s'_node)        
    {
        assert get_upperlimit_decided_instances(s'_node) == get_upperlimit_decided_instances(s_node);

        forall an |
            && an in s.sequence_attestation_duties_to_be_served.Values 
            && an.node == n 
            && an.attestation_duty.slot < get_upperlimit_decided_instances(s'_node)     
        ensures 
                var slot := an.attestation_duty.slot;
                && s.consensus_on_attestation_data[slot].decided_value.isPresent()
                && construct_SlashingDBAttestation_from_att_data(s.consensus_on_attestation_data[slot].decided_value.safe_get()) in s'_node.attestation_slashing_db                   
        {
            var slot := an.attestation_duty.slot;

            assert && s.consensus_on_attestation_data[slot].decided_value.isPresent();

            assert
                && construct_SlashingDBAttestation_from_att_data(s.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_node.attestation_slashing_db
                ;     

            assert
                && construct_SlashingDBAttestation_from_att_data(s.consensus_on_attestation_data[slot].decided_value.safe_get()) in s'_node.attestation_slashing_db
                ;                                         
                    
        }            
  
        
    }        

    predicate lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s: DVState) 
    {
        && inv_quorum_constraints(s)
        && inv_unchanged_honesty(s)
        && inv_only_dv_construct_signed_attestation_signature(s)
        && inv_queued_att_duty_is_rcvd_duty3(s)    
        && invNetwork(s)
        && inv_decided_values_of_previous_duties_are_known_new(s) //
        && inv_exists_decided_value_for_every_duty_before_queued_duties(s) //
        && inv_db_of_validity_predicate_contains_all_previous_decided_values_b(s) //
        && inv_g_d_a(s) //
        && inv_attestation_duty_queue_is_ordered_3(s) //  
        && inv_attestation_duty_queue_is_ordered_4(s) //    
        && inv_g_a_iii(s) //
        && inv_g_a_iv_a(s) //
        && concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s) //
        && pred_data_of_att_share_is_decided_value(s) //  
        && is_sequence_attestation_duties_to_be_served_orderd(s) //
        && pred_inv_current_latest_attestation_duty_match(s)


        && inv_db_of_validity_predicate_contains_all_previous_decided_values(s) 

        && construct_signed_attestation_signature_assumptions_helper(
            s.construct_signed_attestation_signature,
            s.dv_pubkey,
            s.all_nodes
        )    
        && pred_rcvd_attestation_shares_is_in_all_messages_sent(s) 
        && inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
        && inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)      
        && inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)    
        && inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist(s)    
        && inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc(s)         
    }

    lemma lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_summary(
        s: DVState,
        event: DV.Event,
        s': DVState        
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s)
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3a(s, event, s', s_node, node);
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3c(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_1(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_2(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_3(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_4(s, event, s', s_node, node);

                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_multiple(s, event, s', s_node, node);

                // lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s, event, s');
                // lem_pred_data_of_att_share_is_decided_value(s, event, s');

                lem_inv_sequence_attestation_duties_to_be_served_orderd(s, event, s');

                // assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s', node, s_node);
                // assert inv_g_d_a_body_body(s', node, s_node);
                // assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(s', node, s_node);
                // assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                // assert inv_g_a_iii_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                // assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node);
                // assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                // assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');
                // assert pred_data_of_att_share_is_decided_value(s');             
                // assert inv_g_a_iv_a_body_body(s', node, s_node);
        }        
    }   

    lemma lem_NonServeAttstationDuty(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')      
    requires event.HonestNodeTakingStep?
    requires !event.event.ServeAttstationDuty?
    ensures s'.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;
    ensures s'.sequence_attestation_duties_to_be_served == s'.sequence_attestation_duties_to_be_served  
    {
     
    }    
    
    lemma lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s)
    ensures inv_decided_values_of_previous_duties_are_known_new(s');  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3a(s, event, s', s_node, node);
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3c(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_1(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_2(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_3(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_4(s, event, s', s_node, node);

                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_multiple(s, event, s', s_node, node);

                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s, event, s');
                lem_pred_data_of_att_share_is_decided_value(s, event, s');

                lem_inv_sequence_attestation_duties_to_be_served_orderd(s, event, s');

                assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s', node, s_node);
                assert inv_g_d_a_body_body(s', node, s_node);
                assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(s', node, s_node);
                assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_g_a_iii_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node);
                assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');
                assert pred_data_of_att_share_is_decided_value(s');             
                assert inv_g_a_iv_a_body_body(s', node, s_node);
                assert is_sequence_attestation_duties_to_be_served_orderd(s');

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lem_ServeAttstationDuty2(s, event, s');
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s', node, s'_node);                     
 
                              

                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper5(s, event, s');                 
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s', node, s'_node);                        
               
                   
                    case ReceivedAttestationShare(attestation_share) => 
                        lem_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_easy(s', event, s_node, s'_node, node );
                        

                    case ImportedNewBlock(block) => 
                        var s_node2 := add_block_to_bn(s_node, nodeEvent.block);
                        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node, s_node2);
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s', node, s'_node);                     
                    
                 
                    case ResendAttestationShares => 
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_easy(s', event, s_node, s'_node, node );

                   
                    case NoEvent => 
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_easy(s', event, s_node, s'_node, node );
                }
                assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s', node, s'_node);  
                

                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s', hn, s'.honest_nodes_states[hn]); 
                {
                    if hn != node 
                    {
                        // lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3(s, event, s', s.honest_nodes_states[hn]);
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3a(s, event, s', s.honest_nodes_states[hn], hn);
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_easy(s', event, s.honest_nodes_states[hn], s'.honest_nodes_states[hn], hn);
                        // assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s', hn, s'.honest_nodes_states[hn]);                        
                    }
                }     
                assert inv_decided_values_of_previous_duties_are_known_new(s');                  
        

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                 forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s', hn, s'.honest_nodes_states[hn]); 
                {

                    {
                        // lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3(s, event, s', s.honest_nodes_states[hn]);
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3a(s, event, s', s.honest_nodes_states[hn], hn);
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_easy(s', event, s.honest_nodes_states[hn], s'.honest_nodes_states[hn], hn);
                        // assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s', hn, s'.honest_nodes_states[hn]);                        
                    }
                }     
                assert inv_decided_values_of_previous_duties_are_known_new(s'); 

        }
    }      

    lemma lem_inv_exists_decided_value_for_every_duty_before_queued_duties_f_serve_attestation_duty(
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
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, process)
    requires inv_g_a_iii_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_g_d_a_body_body(dv, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process) 
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)  
    requires is_sequence_attestation_duties_to_be_served_orderd(dv);
    requires lem_ServeAttstationDuty2_predicate(dv, index_next_attestation_duty_to_be_served, attestation_duty, n)
    ensures inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, s');
    {
        var new_p := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
        );

        if |process.attestation_duties_queue| == 0 
        {
            assert inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, new_p);  
        }
        else 
        {
            forall i: nat, k, l, t  |
                inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                    dv,
                    n, 
                    new_p,
                    i,
                    k, 
                    l, 
                    t
                )
            ensures 
                new_p.attestation_duties_queue[i-1].slot == dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot      
            {
                // assert process.attestation_duties_queue != [];
                assert i > 0;


                if i != |new_p.attestation_duties_queue| - 1
                {
                    assert inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                        dv,
                        n, 
                        process,
                        i,
                        k, 
                        l, 
                        t                        
                    );
                }
                else 
                {
                    assert new_p.attestation_duties_queue[i-1] == process.attestation_duties_queue[|process.attestation_duties_queue|-1];

                    assert l == index_next_attestation_duty_to_be_served-1;

                    assert new_p.attestation_duties_queue[i-1].slot <= dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;

                    assert inv_attestation_duty_queue_is_ordered_4_body_body_premise(dv, n, process, t, index_next_attestation_duty_to_be_served-1);

                    assert new_p.attestation_duties_queue[i-1].slot == dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;
                }

            }   
        }



        lem_inv_exists_decided_value_for_every_duty_before_queued_duties_f_check_for_next_queued_duty(new_p, s', dv, n, index_next_attestation_duty_to_be_served);
    }

    lemma lem_inv_exists_decided_value_for_every_duty_before_queued_duties_f_att_consensus_decided(
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
    requires inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, process)
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, process)
    requires inv_g_a_iv_a_body_body(dv, n, process)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dv, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process)   
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)

    requires dv.consensus_on_attestation_data[id].decided_value.isPresent()
    requires dv.consensus_on_attestation_data[id].decided_value.safe_get() ==  decided_attestation_data 
    ensures inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, s'); 
    {
        if  && process.current_attestation_duty.isPresent()
            && id == process.current_attestation_duty.safe_get().slot
        {
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

            assert s_mod.attestation_duties_queue == process.attestation_duties_queue;

            lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process, s_mod);

            assert get_upperlimit_decided_instances(s_mod) == process.latest_attestation_duty.safe_get().slot + 1;

            if
                &&  |s_mod.attestation_duties_queue| > 0 
                &&   !s_mod.current_attestation_duty.isPresent()        
            {
                forall an |
                    && an in dv.sequence_attestation_duties_to_be_served.Values 
                    && an.node == n 
                    && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot   
                ensures      
                        var slot := an.attestation_duty.slot;
                            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                        
                {
                    var slot := an.attestation_duty.slot;

                    if slot > s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                    
                    }
                    else if slot == s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                         
                    }
                    else 
                    {
                        assert slot < s_mod.latest_attestation_duty.safe_get().slot;
                        assert 
                            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                           
                    }

                }
            }
            assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, s_mod);


            lem_inv_exists_decided_value_for_every_duty_before_queued_duties_f_check_for_next_queued_duty(s_mod, s', dv, n, index_next_attestation_duty_to_be_served);  
        }
           
    }  

    lemma lem_inv_exists_decided_value_for_every_duty_before_queued_duties_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        s': DVCState,
        dv': DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv', n, process)
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv', n, process)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv', n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dv', n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv', n, process) 
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)
    requires concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv')
    requires pred_data_of_att_share_is_decided_value(dv')
    requires inv_g_a_iv_a_body_body(dv', n, process)
    requires pred_axiom_is_my_attestation_2(dv', process, block)
    ensures inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv', n, s');
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var new_process :=
                process.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );                     

        if new_process.current_attestation_duty.isPresent() && new_process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            // Stop(current_attestation_duty.safe_get().slot);
            var decided_attestation_data := att_consensus_instances_already_decided[new_process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(new_process.attestation_slashing_db, decided_attestation_data);
            var s_mod := new_process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    new_process.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );

            lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dv', n, process, s_mod);


            lem_f_listen_for_new_imported_blocks_helper_1(
                dv',
                process,
                block,
                new_consensus_instances_already_decided
            );

            assert 
                && dv'.consensus_on_attestation_data[new_process.current_attestation_duty.safe_get().slot].decided_value.isPresent()
                && dv'.consensus_on_attestation_data[new_process.current_attestation_duty.safe_get().slot].decided_value.safe_get() == decided_attestation_data
            ;                        

            assert inv_g_d_a_body_body(dv', n, s_mod);                  

            assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv', n, s_mod);


            if
                &&  |s_mod.attestation_duties_queue| > 0 
                &&   !s_mod.current_attestation_duty.isPresent()        
            {
                forall an |
                    && an in dv'.sequence_attestation_duties_to_be_served.Values 
                    && an.node == n 
                    && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot   
                ensures      
                        var slot := an.attestation_duty.slot;
                            && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                        
                {
                    var slot := an.attestation_duty.slot;

                    if slot > s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                    
                    }
                    else if slot == s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                         
                    }
                    else 
                    {
                        assert slot < s_mod.latest_attestation_duty.safe_get().slot;
                        assert 
                            && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                           
                    }

                }
            }
            assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv', n, s_mod);                 

            forall an |
                && an in dv'.sequence_attestation_duties_to_be_served.Values 
                && an.node == n 
                && an.attestation_duty.slot < get_upperlimit_decided_instances(s_mod)
            {
                if an.attestation_duty.slot < get_upperlimit_decided_instances(process)
                {

                }
                else 
                {
                    assert an.attestation_duty.slot == new_process.current_attestation_duty.safe_get().slot;
                }
            }            

            
            lem_inv_exists_decided_value_for_every_duty_before_queued_duties_f_check_for_next_queued_duty(s_mod, s', dv', n, index_next_attestation_duty_to_be_served);                    
        }        
    }   

    lemma lem_inv_exists_decided_value_for_every_duty_before_queued_duties_f_check_for_next_queued_duty_helper_1(
        process: DVCState,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat,
        s_mod: DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state  
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, process)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dv, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process)  
    requires && first_queued_att_duty_was_decided_or_ready_to_be_served(process)    
             && first_queued_att_duty_was_decided(process)
             && s_mod == f_dequeue_attestation_duties_queue(process)
    ensures ( && |s_mod.attestation_duties_queue| > 0 
              &&   !s_mod.current_attestation_duty.isPresent()
            )
            ==>
            inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, s_mod)
    {
        if  && |s_mod.attestation_duties_queue| > 0 
            && !s_mod.current_attestation_duty.isPresent()
        {
            
            forall an |
                && an in dv.sequence_attestation_duties_to_be_served.Values 
                && an.node == n 
                && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot
            ensures 
                var slot := an.attestation_duty.slot;
                && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
            ;                          
            {
                var slot := an.attestation_duty.slot;
            
                if an.attestation_duty.slot < process.attestation_duties_queue[0].slot  
                {
                    assert 
                        && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                    ;
                }
                else 
                {
                    var t :|  dv.sequence_attestation_duties_to_be_served[t] == an;
                    assert process.attestation_duties_queue[0] in process.attestation_duties_queue;
                    var i :|  
                            && dv.sequence_attestation_duties_to_be_served[i].node == n 
                            && dv.sequence_attestation_duties_to_be_served[i].attestation_duty == process.attestation_duties_queue[0];
                    assert process.attestation_duties_queue[1] in process.attestation_duties_queue;
                    var j :|  
                            && dv.sequence_attestation_duties_to_be_served[j].node == n 
                            && dv.sequence_attestation_duties_to_be_served[j].attestation_duty == process.attestation_duties_queue[1];   

                    lem_inv_attestation_duty_queue_is_ordered_3_body_body(
                        dv,
                        n,
                        process,
                        1,
                        i,
                        j,
                        t
                    ); 

                
                    assert 
                        && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                    ;
                    
                }
            }                  
        }
    }

    

    lemma lem_inv_exists_decided_value_for_every_duty_before_queued_duties_f_check_for_next_queued_duty(
        process: DVCState,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state  
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, process)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dv, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process)  
    ensures inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, s')
    decreases process.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(process)    
        {
            if first_queued_att_duty_was_decided(process)
            {
                var s_mod := f_dequeue_attestation_duties_queue(process);

                lem_f_check_for_next_queued_duty_helper(
                        process,
                        dv,
                        n,
                        index_next_attestation_duty_to_be_served,
                        s_mod
                );

                lem_inv_exists_decided_value_for_every_duty_before_queued_duties_f_check_for_next_queued_duty(s_mod, s', dv, n , index_next_attestation_duty_to_be_served);
            }
            else 
            {
                var new_process := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..]
                );   

                var queue_head := process.attestation_duties_queue[0];       


                assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, s');

            }
        } 
        else 
        {
            // assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, s');
        }       
    }       

    lemma lem_inv_exists_decided_value_for_every_duty_before_queued_duties_helper_easy(
        s: DVState,
        event: DV.Event,
        s_node: DVCState,
        s'_node: DVCState,
        n: BLSPubkey
    )
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(s, n, s_node)
    requires s_node.attestation_duties_queue == s'_node.attestation_duties_queue
    requires s_node.current_attestation_duty == s'_node.current_attestation_duty
    requires s_node.attestation_slashing_db <= s'_node.attestation_slashing_db
    ensures inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(s, n, s'_node)        
    {        
    }       

    lemma lem_inv_exists_decided_value_for_every_duty_before_queued_duties(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s)
    ensures inv_exists_decided_value_for_every_duty_before_queued_duties(s');  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3a(s, event, s', s_node, node);
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3c(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_1(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_2(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_3(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_4(s, event, s', s_node, node);

                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_multiple(s, event, s', s_node, node);

                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s, event, s');
                lem_pred_data_of_att_share_is_decided_value(s, event, s');

                lem_inv_sequence_attestation_duties_to_be_served_orderd(s, event, s');

                assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s', node, s_node);
                assert inv_g_d_a_body_body(s', node, s_node);
                assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(s', node, s_node);
                assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_g_a_iii_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node);
                assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');
                assert pred_data_of_att_share_is_decided_value(s');             
                assert inv_g_a_iv_a_body_body(s', node, s_node);
                assert is_sequence_attestation_duties_to_be_served_orderd(s');

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lem_ServeAttstationDuty2(s, event, s');
                        lem_inv_exists_decided_value_for_every_duty_before_queued_duties_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(s', node, s'_node);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper5(s, event, s');                 
                        lem_inv_exists_decided_value_for_every_duty_before_queued_duties_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(s', node, s'_node);                        
               
                   
                    case ReceivedAttestationShare(attestation_share) => 
                        lem_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        lem_inv_exists_decided_value_for_every_duty_before_queued_duties_helper_easy(s', event, s_node, s'_node, node );
                        

                    case ImportedNewBlock(block) => 
                        var s_node2 := add_block_to_bn(s_node, nodeEvent.block);
                        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node, s_node2);
                        lem_inv_exists_decided_value_for_every_duty_before_queued_duties_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(s', node, s'_node);                     
                    
                 
                    case ResendAttestationShares => 
                        lem_f_resend_attestation_share_constants(s_node, s'_node);
                        lem_inv_exists_decided_value_for_every_duty_before_queued_duties_helper_easy(s', event, s_node, s'_node, node );

                   
                    case NoEvent => 
                        lem_inv_exists_decided_value_for_every_duty_before_queued_duties_helper_easy(s', event, s_node, s'_node, node );
                }
                assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(s', node, s'_node);  
                

                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_1(s, event, s', s.honest_nodes_states[hn], hn);
                        lem_inv_exists_decided_value_for_every_duty_before_queued_duties_helper_easy(s', event, s.honest_nodes_states[hn], s'.honest_nodes_states[hn], hn);
                    }
                }     
                assert inv_exists_decided_value_for_every_duty_before_queued_duties(s');                  
        

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    // if hn != node 
                    // {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_1(s, event, s', s.honest_nodes_states[hn], hn);
                        lem_inv_exists_decided_value_for_every_duty_before_queued_duties_helper_easy(s', event, s.honest_nodes_states[hn], s'.honest_nodes_states[hn], hn);
                    // }
                }     
                assert inv_exists_decided_value_for_every_duty_before_queued_duties(s'); 

        }
    }    

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_f_serve_attestation_duty(
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
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, process)
    requires inv_g_a_iii_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_g_d_a_body_body(dv, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process) 
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)  
    requires is_sequence_attestation_duties_to_be_served_orderd(dv);
    requires lem_ServeAttstationDuty2_predicate(dv, index_next_attestation_duty_to_be_served, attestation_duty, n)
    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, s', index_next_attestation_duty_to_be_served);
    {
        var new_p := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
        );

        if |process.attestation_duties_queue| == 0 
        {
            assert inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, new_p);  
        }
        else 
        {
            forall i: nat, k, l, t  |
                inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                    dv,
                    n, 
                    new_p,
                    i,
                    k, 
                    l, 
                    t
                )
            ensures 
                new_p.attestation_duties_queue[i-1].slot == dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot      
            {
                // assert process.attestation_duties_queue != [];
                assert i > 0;


                if i != |new_p.attestation_duties_queue| - 1
                {
                    assert inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                        dv,
                        n, 
                        process,
                        i,
                        k, 
                        l, 
                        t                        
                    );
                }
                else 
                {
                    assert new_p.attestation_duties_queue[i-1] == process.attestation_duties_queue[|process.attestation_duties_queue|-1];

                    assert l == index_next_attestation_duty_to_be_served-1;

                    assert new_p.attestation_duties_queue[i-1].slot <= dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;

                    assert inv_attestation_duty_queue_is_ordered_4_body_body_premise(dv, n, process, t, index_next_attestation_duty_to_be_served-1);

                    assert new_p.attestation_duties_queue[i-1].slot == dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;
                }

            }   
        }



        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_f_check_for_next_queued_duty(new_p, s', dv, n, index_next_attestation_duty_to_be_served);
    }

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_f_att_consensus_decided(
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
    requires inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, process)
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, process)
    requires inv_g_a_iv_a_body_body(dv, n, process)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dv, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process)   
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)

    requires dv.consensus_on_attestation_data[id].decided_value.isPresent()
    requires dv.consensus_on_attestation_data[id].decided_value.safe_get() ==  decided_attestation_data 
    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, s', index_next_attestation_duty_to_be_served); 
    {  
        if  && process.current_attestation_duty.isPresent()
            && id == process.current_attestation_duty.safe_get().slot
        {
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

            assert s_mod.attestation_duties_queue == process.attestation_duties_queue;

            lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process, s_mod);

            assert get_upperlimit_decided_instances(s_mod) == process.latest_attestation_duty.safe_get().slot + 1;

            if
                &&  |s_mod.attestation_duties_queue| > 0 
                &&   !s_mod.current_attestation_duty.isPresent()        
            {
                forall an |
                    && an in dv.sequence_attestation_duties_to_be_served.Values 
                    && an.node == n 
                    && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot   
                ensures      
                        var slot := an.attestation_duty.slot;
                            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                        
                {
                    var slot := an.attestation_duty.slot;

                    if slot > s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                    
                    }
                    else if slot == s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                         
                    }
                    else 
                    {
                        assert slot < s_mod.latest_attestation_duty.safe_get().slot;
                        assert 
                            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                           
                    }

                }
            }
            assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, s_mod);


            lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_f_check_for_next_queued_duty(s_mod, s', dv, n, index_next_attestation_duty_to_be_served); 
        }
    } 

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        s': DVCState,
        dv': DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv', n, process)
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv', n, process)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv', n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dv', n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv', n, process) 
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)
    requires concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv')
    requires pred_data_of_att_share_is_decided_value(dv')
    requires inv_g_a_iv_a_body_body(dv', n, process)
    requires pred_axiom_is_my_attestation_2(dv', process, block)
    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv', n, s', index_next_attestation_duty_to_be_served);
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var new_process :=
                process.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );                     

        if new_process.current_attestation_duty.isPresent() && new_process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            // Stop(current_attestation_duty.safe_get().slot);
            var decided_attestation_data := att_consensus_instances_already_decided[new_process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(new_process.attestation_slashing_db, decided_attestation_data);
            var s_mod := new_process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    new_process.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );

            lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dv', n, process, s_mod);


            lem_f_listen_for_new_imported_blocks_helper_1(
                dv',
                process,
                block,
                new_consensus_instances_already_decided
            );

            assert 
                && dv'.consensus_on_attestation_data[new_process.current_attestation_duty.safe_get().slot].decided_value.isPresent()
                && dv'.consensus_on_attestation_data[new_process.current_attestation_duty.safe_get().slot].decided_value.safe_get() == decided_attestation_data
            ;                        

            assert inv_g_d_a_body_body(dv', n, s_mod);                  

            assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv', n, s_mod);


            if
                &&  |s_mod.attestation_duties_queue| > 0 
                &&   !s_mod.current_attestation_duty.isPresent()        
            {
                forall an |
                    && an in dv'.sequence_attestation_duties_to_be_served.Values 
                    && an.node == n 
                    && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot   
                ensures      
                        var slot := an.attestation_duty.slot;
                            && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                        
                {
                    var slot := an.attestation_duty.slot;

                    if slot > s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                    
                    }
                    else if slot == s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                         
                    }
                    else 
                    {
                        assert slot < s_mod.latest_attestation_duty.safe_get().slot;
                        assert 
                            && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                           
                    }

                }
            }
            assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv', n, s_mod);                 

            forall an |
                && an in dv'.sequence_attestation_duties_to_be_served.Values 
                && an.node == n 
                && an.attestation_duty.slot < get_upperlimit_decided_instances(s_mod)
            {
                if an.attestation_duty.slot < get_upperlimit_decided_instances(process)
                {

                }
                else 
                {
                    assert an.attestation_duty.slot == new_process.current_attestation_duty.safe_get().slot;
                }
            }            

            
            lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_f_check_for_next_queued_duty(s_mod, s', dv', n, index_next_attestation_duty_to_be_served);                    
        }        
    }   


    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_f_check_for_next_queued_duty(
        process: DVCState,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state  
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, process)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dv, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process)  
    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, s', index_next_attestation_duty_to_be_served)
    decreases process.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(process)       
        {
            if first_queued_att_duty_was_decided(process)
            {
                var s_mod := f_dequeue_attestation_duties_queue(process);

                lem_f_check_for_next_queued_duty_helper(
                    process,
                    dv,
                    n,
                    index_next_attestation_duty_to_be_served,
                    s_mod
                );                         

                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_f_check_for_next_queued_duty(s_mod, s', dv, n , index_next_attestation_duty_to_be_served);
            }
            else 
            {
                var new_process := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..]
                );   

                var queue_head := process.attestation_duties_queue[0];       

                assert s'.attestation_duties_queue == process.attestation_duties_queue[1..];

                assert forall ad  |
                    && ad in s'.attestation_duties_queue  :: ad in process.attestation_duties_queue;            

                assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, s', index_next_attestation_duty_to_be_served);

            }
        } 
        else 
        {
            // assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, s');
        }       
    }             

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_helper_easy(
        s: DVState,
        event: DV.Event,
        s_node: DVCState,
        s'_node: DVCState,
        n: BLSPubkey
    )
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s, n, s_node, s.index_next_attestation_duty_to_be_served)
    requires s_node.attestation_duties_queue == s'_node.attestation_duties_queue
    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s, n, s'_node, s.index_next_attestation_duty_to_be_served)        
    {        
    }    

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_dv_next_helper_honest(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s)
    requires event.HonestNodeTakingStep?
    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', event.node, s'.honest_nodes_states[event.node], s'.index_next_attestation_duty_to_be_served); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3a(s, event, s', s_node, node);
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3c(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_1(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_2(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_3(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_4(s, event, s', s_node, node);

                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_multiple(s, event, s', s_node, node);

                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s, event, s');
                lem_pred_data_of_att_share_is_decided_value(s, event, s');

                lem_inv_sequence_attestation_duties_to_be_served_orderd(s, event, s');

                assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s', node, s_node);
                assert inv_g_d_a_body_body(s', node, s_node);
                assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(s', node, s_node);
                assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_g_a_iii_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node);
                assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');
                assert pred_data_of_att_share_is_decided_value(s');             
                assert inv_g_a_iv_a_body_body(s', node, s_node);
                assert is_sequence_attestation_duties_to_be_served_orderd(s');

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lem_ServeAttstationDuty2(s, event, s');
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        lem_NonServeAttstationDuty(s, event, s');
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper5(s, event, s');                 
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                        
               
                   
                    case ReceivedAttestationShare(attestation_share) =>
                        lem_NonServeAttstationDuty(s, event, s'); 
                        lem_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  
                        

                    case ImportedNewBlock(block) => 
                        lem_NonServeAttstationDuty(s, event, s');
                        var s_node2 := add_block_to_bn(s_node, nodeEvent.block);
                        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node, s_node2);
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                     
                    
                 
                    case ResendAttestationShares => 
                        lem_NonServeAttstationDuty(s, event, s');
                        lem_f_resend_attestation_share_constants(s_node, s'_node);
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  

                    case NoEvent => 
                        lem_NonServeAttstationDuty(s, event, s');
                        assert s_node == s'_node; 
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                          
                }
                // assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  
        }
    }      

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_helper_easy_2(
        s': DVState
    )
    requires forall hn |
                        && hn in s'.honest_nodes_states.Keys   
                    :: inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', hn, s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served); 
    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_b(s')
    {

    }                 

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_dv_next(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s)
    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_b(s');  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_dv_next_helper_honest(s, event, s');
                   
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', hn, s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_multiple(s, event, s', s.honest_nodes_states[hn], hn);
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_helper_easy(s', event, s.honest_nodes_states[hn], s'.honest_nodes_states[hn], hn);
                    }
                }  

                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_helper_easy_2(s');
                         
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', hn, s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served); 
                {
                    // if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_multiple(s, event, s', s.honest_nodes_states[hn], hn);
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_b_helper_easy(s', event, s.honest_nodes_states[hn], s'.honest_nodes_states[hn], hn);
                    }
                }     
                assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b(s');  

        }
    }    

    lemma lem_inv_g_d_a_f_serve_attestation_duty(
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
    requires inv_g_d_a_body_body(dv, n, process)
    ensures inv_g_d_a_body_body(dv, n, s');
    {
        var new_p := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
        );

        lem_inv_g_d_a_f_check_for_next_queued_duty(new_p, s', dv, n);
    }    

    lemma lem_inv_g_d_a_f_att_consensus_decided(
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
    requires inv_g_d_a_body_body(dv, n, process)
    ensures inv_g_d_a_body_body(dv, n, s'); 
    {
        if  && process.current_attestation_duty.isPresent()
            && id == process.current_attestation_duty.safe_get().slot
        {
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

            lem_inv_g_d_a_f_check_for_next_queued_duty(s_mod, s', dv, n);     
        }   
        
    }  

    lemma lem_inv_g_d_a_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        s': DVCState,
        dv': DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires inv_g_d_a_body_body(dv', n, process)
    requires concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv')
    requires pred_data_of_att_share_is_decided_value(dv')
    requires pred_axiom_is_my_attestation_2(dv', process, block)
    ensures inv_g_d_a_body_body(dv', n, s');
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var new_process :=
                process.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );    

        lem_f_listen_for_new_imported_blocks_helper_1(
            dv',
            process,
            block,
            new_consensus_instances_already_decided
        );                                    

        if new_process.current_attestation_duty.isPresent() && new_process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            // Stop(current_attestation_duty.safe_get().slot);
            var decided_attestation_data := att_consensus_instances_already_decided[new_process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(new_process.attestation_slashing_db, decided_attestation_data);
            var s_mod := new_process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    new_process.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );
            
            lem_inv_g_d_a_f_check_for_next_queued_duty(s_mod, s', dv', n);   
        }      
    }      


    lemma lem_inv_g_d_a_f_check_for_next_queued_duty(
        process: DVCState,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state  
    requires inv_g_d_a_body_body(dv, n, process)
    ensures inv_g_d_a_body_body(dv, n, s')
    decreases process.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(process)     
        {
            if first_queued_att_duty_was_decided(process)
            {
                var s_mod := f_dequeue_attestation_duties_queue(process);

                lem_inv_g_d_a_f_check_for_next_queued_duty(s_mod, s', dv, n );
            }
            else 
            {        
                assert inv_g_d_a_body_body(dv, n, s');

            }
        } 
        else 
        {
        }       
    } 

    lemma lem_inv_g_d_a_helper_honest(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')     
    requires lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s)  
    requires event.HonestNodeTakingStep?
    ensures inv_g_d_a_body_body(s', event.node, s'.honest_nodes_states[event.node]); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                // lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3a(s, event, s', s_node, node);
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3c(s, event, s', s_node, node);
                // lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_1(s, event, s', s_node, node);
                // lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_2(s, event, s', s_node, node);
                // lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_3(s, event, s', s_node, node);
                // lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_4(s, event, s', s_node, node);

                // lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_multiple(s, event, s', s_node, node);

                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s, event, s');
                lem_pred_data_of_att_share_is_decided_value(s, event, s');

                // lem_inv_sequence_attestation_duties_to_be_served_orderd(s, event, s');

                // assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s', node, s_node);
                assert inv_g_d_a_body_body(s', node, s_node);
                // assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(s', node, s_node);
                // assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                // assert inv_g_a_iii_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                // assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node);
                // assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');
                assert pred_data_of_att_share_is_decided_value(s');             
                // assert inv_g_a_iv_a_body_body(s', node, s_node);
                // assert is_sequence_attestation_duties_to_be_served_orderd(s');

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lem_ServeAttstationDuty2(s, event, s');
                        lem_inv_g_d_a_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_g_d_a_body_body(s', node, s'_node);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        lem_NonServeAttstationDuty(s, event, s');
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper5(s, event, s');                 
                        lem_inv_g_d_a_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_g_d_a_body_body(s', node, s'_node);                        
               
                   
                    case ReceivedAttestationShare(attestation_share) =>
                        lem_NonServeAttstationDuty(s, event, s'); 
                        lem_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        // lem_inv_g_d_a_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_d_a_body_body(s', node, s'_node);  
                        

                    case ImportedNewBlock(block) => 
                        lem_NonServeAttstationDuty(s, event, s');
                        var s_node2 := add_block_to_bn(s_node, nodeEvent.block);
                        lem_inv_g_d_a_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_g_d_a_body_body(s', node, s'_node);                     
                    
                 
                    case ResendAttestationShares => 
                        lem_NonServeAttstationDuty(s, event, s');
                        lem_f_resend_attestation_share_constants(s_node, s'_node);
                        // lem_inv_g_d_a_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_d_a_body_body(s', node, s'_node);  

                    case NoEvent => 
                        lem_NonServeAttstationDuty(s, event, s');
                        assert s_node == s'_node; 
                        // lem_inv_g_d_a_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_d_a_body_body(s', node, s'_node);                          
                }
                // assert inv_g_d_a_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  
        }
    }     

    lemma lem_inv_g_d_a(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s)
    ensures inv_g_d_a(s');  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_g_d_a_helper_honest(s, event, s');
                   
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_g_d_a_body_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3c(s, event, s', s.honest_nodes_states[hn], hn);
                    }
                }  
                assert inv_g_d_a(s');
                         
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_g_d_a_body_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    // if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3c(s, event, s', s.honest_nodes_states[hn], hn);
                    }
                }  
                assert inv_g_d_a(s');

        }
    }  

    lemma lem_inv_attestation_duty_queue_is_ordered_3_f_serve_attestation_duty(
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
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process) 
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)  
    requires is_sequence_attestation_duties_to_be_served_orderd(dv);
    requires lem_ServeAttstationDuty2_predicate(dv, index_next_attestation_duty_to_be_served, attestation_duty, n)
    ensures inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, s');
    {
        var new_p := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
        );

        if |process.attestation_duties_queue| == 0 
        {
            assert inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, new_p);  
        }
        else 
        {
            forall i: nat, k, l, t  |
                inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                    dv,
                    n, 
                    new_p,
                    i,
                    k, 
                    l, 
                    t
                )
            ensures 
                new_p.attestation_duties_queue[i-1].slot == dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot      
            {
                // assert process.attestation_duties_queue != [];
                assert i > 0;


                if i != |new_p.attestation_duties_queue| - 1
                {
                    assert inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                        dv,
                        n, 
                        process,
                        i,
                        k, 
                        l, 
                        t                        
                    );
                }
                else 
                {
                    assert new_p.attestation_duties_queue[i-1] == process.attestation_duties_queue[|process.attestation_duties_queue|-1];

                    assert l == index_next_attestation_duty_to_be_served-1;

                    assert new_p.attestation_duties_queue[i-1].slot <= dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;

                    assert inv_attestation_duty_queue_is_ordered_4_body_body_premise(dv, n, process, t, index_next_attestation_duty_to_be_served-1);

                    assert new_p.attestation_duties_queue[i-1].slot == dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;
                }

            }   
        }        

        lem_inv_attestation_duty_queue_is_ordered_3_f_check_for_next_queued_duty(new_p, s', dv, n);
    }     

    lemma lem_inv_attestation_duty_queue_is_ordered_3_f_att_consensus_decided(
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
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process)
    ensures inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, s'); 
    { 
        if  && process.current_attestation_duty.isPresent()
            && id == process.current_attestation_duty.safe_get().slot
        {
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

            lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process, s_mod);
            lem_inv_attestation_duty_queue_is_ordered_3_f_check_for_next_queued_duty(s_mod, s', dv, n);   
        }          
    }  

    lemma lem_inv_attestation_duty_queue_is_ordered_3_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        s': DVCState,
        dv': DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv', n, process)
    ensures inv_attestation_duty_queue_is_ordered_3_body_body(dv', n, s')
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var new_process :=
                process.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );    
                                 

        if new_process.current_attestation_duty.isPresent() && new_process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            // Stop(current_attestation_duty.safe_get().slot);
            var decided_attestation_data := att_consensus_instances_already_decided[new_process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(new_process.attestation_slashing_db, decided_attestation_data);
            var s_mod := new_process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    new_process.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );
            
            lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dv', n, process, s_mod);
            lem_inv_attestation_duty_queue_is_ordered_3_f_check_for_next_queued_duty(s_mod, s', dv', n);
        } 
        else 
        {
            lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dv', n, process, s');           
        }     
    }           

    lemma lem_inv_attestation_duty_queue_is_ordered_3_f_check_for_next_queued_duty(
        process: DVCState,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state  
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process)
    ensures inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, s')
    decreases process.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(process)        
        {
            if first_queued_att_duty_was_decided(process)
            {
                var s_mod := f_dequeue_attestation_duties_queue(process);

                lemma3_inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process, s_mod);
                lem_inv_attestation_duty_queue_is_ordered_3_f_check_for_next_queued_duty(s_mod, s', dv, n );
            }
            else 
            {        
                lemma3_inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process, s');
                assert inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, s');

            }
        } 
        else 
        {
            assert inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, s');
        }       
    }  

    lemma lem_inv_attestation_duty_queue_is_ordered_3_honest(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')     
    requires 
        && inv_attestation_duty_queue_is_ordered_3(s) //  
        && inv_attestation_duty_queue_is_ordered_4(s) //    
        && is_sequence_attestation_duties_to_be_served_orderd(s) //     
    requires event.HonestNodeTakingStep?
    ensures inv_attestation_duty_queue_is_ordered_3_body_body(s', event.node, s'.honest_nodes_states[event.node]) 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];

                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_3(s, event, s', s_node, node);
                lem_inv_sequence_attestation_duties_to_be_served_orderd(s, event, s');

                assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node);
                assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lem_ServeAttstationDuty2(s, event, s');
                        lem_inv_attestation_duty_queue_is_ordered_3_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s'_node);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        lem_NonServeAttstationDuty(s, event, s');
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lem_inv_attestation_duty_queue_is_ordered_3_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s'_node);                        
               
                   
                    case ReceivedAttestationShare(attestation_share) =>
                        lem_NonServeAttstationDuty(s, event, s'); 
                        lem_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node, s'_node);
                        assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s'_node);  
                        

                    case ImportedNewBlock(block) => 
                        lem_NonServeAttstationDuty(s, event, s');
                        var s_node2 := add_block_to_bn(s_node, nodeEvent.block);
                        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node, s_node2);
                        lem_inv_attestation_duty_queue_is_ordered_3_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s'_node);                     
                    
                 
                    case ResendAttestationShares => 
                        lem_NonServeAttstationDuty(s, event, s');
                        lem_f_resend_attestation_share_constants(s_node, s'_node);
                        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node, s'_node);
                        assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s'_node); 

                    case NoEvent => 
                        lem_NonServeAttstationDuty(s, event, s');
                        assert s_node == s'_node; 
                        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node, s'_node);
                        assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s'_node);                          
                }                
        }
    }         


    lemma lem_inv_attestation_duty_queue_is_ordered_3(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires 
        && inv_attestation_duty_queue_is_ordered_3(s) //  
        && inv_attestation_duty_queue_is_ordered_4(s) //    
        && is_sequence_attestation_duties_to_be_served_orderd(s) //    
    ensures inv_attestation_duty_queue_is_ordered_3(s');  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_attestation_duty_queue_is_ordered_3_honest(s, event, s');
                   
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_attestation_duty_queue_is_ordered_3_body_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_3(s, event, s', s.honest_nodes_states[hn], hn);
                        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(s', hn, s.honest_nodes_states[hn], s'.honest_nodes_states[hn]);
                    }
                }  
                         
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_attestation_duty_queue_is_ordered_3_body_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    // if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_3(s, event, s', s.honest_nodes_states[hn], hn);
                        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(s', hn, s.honest_nodes_states[hn], s'.honest_nodes_states[hn]);
                    }
                }   

        }
    }    

    lemma lem_inv_attestation_duty_queue_is_ordered_4_f_serve_attestation_duty(
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
    // requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process) 
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)  
    requires is_sequence_attestation_duties_to_be_served_orderd(dv);
    requires lem_ServeAttstationDuty2_predicate(dv, index_next_attestation_duty_to_be_served, attestation_duty, n)
    ensures inv_attestation_duty_queue_is_ordered_4_body_body(dv, n, s', index_next_attestation_duty_to_be_served);
    {
        var new_p := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
        );

        assert inv_attestation_duty_queue_is_ordered_4_body_body(dv, n, new_p, index_next_attestation_duty_to_be_served);         

        lem_inv_attestation_duty_queue_is_ordered_4_f_check_for_next_queued_duty(new_p, s', dv, n, index_next_attestation_duty_to_be_served);
    } 

    lemma lem_inv_attestation_duty_queue_is_ordered_4_f_att_consensus_decided(
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
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    ensures inv_attestation_duty_queue_is_ordered_4_body_body(dv, n, s', index_next_attestation_duty_to_be_served); 
    {       
        if  && process.current_attestation_duty.isPresent()
            && id == process.current_attestation_duty.safe_get().slot
        {
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

            lemma2_inv_attestation_duty_queue_is_ordered_4_body_body(dv, n, process, s_mod, index_next_attestation_duty_to_be_served);
            lem_inv_attestation_duty_queue_is_ordered_4_f_check_for_next_queued_duty(s_mod, s', dv, n, index_next_attestation_duty_to_be_served);             
        }
    }       

    lemma lem_inv_attestation_duty_queue_is_ordered_4_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        s': DVCState,
        dv': DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dv', n, process, index_next_attestation_duty_to_be_served)
    ensures inv_attestation_duty_queue_is_ordered_4_body_body(dv', n, s', index_next_attestation_duty_to_be_served)
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var new_process :=
                process.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );    
                                 

        if new_process.current_attestation_duty.isPresent() && new_process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            // Stop(current_attestation_duty.safe_get().slot);
            var decided_attestation_data := att_consensus_instances_already_decided[new_process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(new_process.attestation_slashing_db, decided_attestation_data);
            var s_mod := new_process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    new_process.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );
            
            lemma2_inv_attestation_duty_queue_is_ordered_4_body_body(dv', n, process, s_mod, index_next_attestation_duty_to_be_served);
            lem_inv_attestation_duty_queue_is_ordered_4_f_check_for_next_queued_duty(s_mod, s', dv', n, index_next_attestation_duty_to_be_served);
        } 
        else 
        {
            lemma2_inv_attestation_duty_queue_is_ordered_4_body_body(dv', n, process, s', index_next_attestation_duty_to_be_served);           
        }     
    }                 
    
    lemma lem_inv_attestation_duty_queue_is_ordered_4_f_check_for_next_queued_duty(
        process: DVCState,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state  
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dv, n, process, index_next_attestation_duty_to_be_served)  
    ensures inv_attestation_duty_queue_is_ordered_4_body_body(dv, n, s', index_next_attestation_duty_to_be_served)      
    decreases process.attestation_duties_queue
    {
        if first_queued_att_duty_was_decided_or_ready_to_be_served(process)      
        {
            if first_queued_att_duty_was_decided(process)
            {
                var s_mod := f_dequeue_attestation_duties_queue(process);

                lemma3_inv_attestation_duty_queue_is_ordered_4_body_body(dv, n, process, s_mod, index_next_attestation_duty_to_be_served);
                lem_inv_attestation_duty_queue_is_ordered_4_f_check_for_next_queued_duty(s_mod, s', dv, n , index_next_attestation_duty_to_be_served);
            }
            else 
            {
                var new_process := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..]
                );   

                var queue_head := process.attestation_duties_queue[0];      
                lemma3_inv_attestation_duty_queue_is_ordered_4_body_body(dv, n, process, new_process, index_next_attestation_duty_to_be_served);                 


                // assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, s');

            }
        } 
        else 
        {
            lemma2_inv_attestation_duty_queue_is_ordered_4_body_body(dv, n, process, s', index_next_attestation_duty_to_be_served);
        }       
    }     

    lemma lem_inv_attestation_duty_queue_is_ordered_4_honest(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')     
    requires 
        && inv_attestation_duty_queue_is_ordered_3(s) //  
        && inv_attestation_duty_queue_is_ordered_4(s) //  
        && is_sequence_attestation_duties_to_be_served_orderd(s) //     
    requires event.HonestNodeTakingStep?
    ensures inv_attestation_duty_queue_is_ordered_4_body_body(s', event.node, s'.honest_nodes_states[event.node], s'.index_next_attestation_duty_to_be_served) 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];

                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_3(s, event, s', s_node, node);
                lem_inv_sequence_attestation_duties_to_be_served_orderd(s, event, s');

                assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lem_ServeAttstationDuty2(s, event, s');
                        lem_inv_attestation_duty_queue_is_ordered_4_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        lem_NonServeAttstationDuty(s, event, s');
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lem_inv_attestation_duty_queue_is_ordered_4_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                        
               
                   
                    case ReceivedAttestationShare(attestation_share) =>
                        lem_NonServeAttstationDuty(s, event, s'); 
                        lem_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        lemma2_inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s'_node, s'.index_next_attestation_duty_to_be_served);
                        assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  
                        

                    case ImportedNewBlock(block) => 
                        lem_NonServeAttstationDuty(s, event, s');
                        var s_node2 := add_block_to_bn(s_node, nodeEvent.block);
                        lemma2_inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s_node2, s'.index_next_attestation_duty_to_be_served);
                        lem_inv_attestation_duty_queue_is_ordered_4_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                     
                    
                 
                    case ResendAttestationShares => 
                        lem_NonServeAttstationDuty(s, event, s');
                        lem_f_resend_attestation_share_constants(s_node, s'_node);
                        lemma2_inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s'_node, s'.index_next_attestation_duty_to_be_served);
                        assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served); 

                    case NoEvent => 
                        lem_NonServeAttstationDuty(s, event, s');
                        assert s_node == s'_node; 
                        lemma2_inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s'_node, s'.index_next_attestation_duty_to_be_served);
                        assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                          
                }                
        }
    }   

    lemma lem_inv_attestation_duty_queue_is_ordered_4_helper_other_node(
        s: DVState,
        event: DV.Event,
        s': DVState,
        hn: BLSPubkey
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires 
        && inv_attestation_duty_queue_is_ordered_3(s) //  
        && inv_attestation_duty_queue_is_ordered_4(s) //    
        && is_sequence_attestation_duties_to_be_served_orderd(s) //     
    requires event.HonestNodeTakingStep?
    requires event.event.ServeAttstationDuty?
    requires event.node != hn 
    requires hn in s.honest_nodes_states
    ensures inv_attestation_duty_queue_is_ordered_4_body_body(s', hn, s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served)
    {
        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_3(s, event, s', s.honest_nodes_states[hn], hn);

        assert s'.index_next_attestation_duty_to_be_served == s.index_next_attestation_duty_to_be_served + 1;

        assert s.sequence_attestation_duties_to_be_served[s.index_next_attestation_duty_to_be_served].node == event.node;

        var s_nodeh := s.honest_nodes_states[hn];
        var s'_nodeh := s'.honest_nodes_states[hn];

        assert inv_attestation_duty_queue_is_ordered_4_body_body(s', hn, s_nodeh, s.index_next_attestation_duty_to_be_served);

        if |s'_nodeh.attestation_duties_queue| > 0
        {
            assert |s_nodeh.attestation_duties_queue| > 0;

            forall i: nat |
                inv_attestation_duty_queue_is_ordered_4_body_body_premise(
                    s',
                    hn, 
                    s'_nodeh,
                    i,
                    s'.index_next_attestation_duty_to_be_served
                )
            ensures 
                var last := seq_last(s'_nodeh.attestation_duties_queue);
                last.slot == s'.sequence_attestation_duties_to_be_served[i].attestation_duty.slot;
            {
                var last := seq_last(s'_nodeh.attestation_duties_queue);

                var lastp := seq_last(s_nodeh.attestation_duties_queue);

                assert s.sequence_attestation_duties_to_be_served == s'.sequence_attestation_duties_to_be_served;

                // assert last == lastp;

                if i < s.index_next_attestation_duty_to_be_served
                {
                    assert 
                        inv_attestation_duty_queue_is_ordered_4_body_body_premise(
                            s',
                            hn, 
                            s_nodeh,
                            i,
                            s.index_next_attestation_duty_to_be_served
                        );
                    assert lastp.slot == s'.sequence_attestation_duties_to_be_served[i].attestation_duty.slot; 
                    assert last == lastp;
                }
                else 
                {
                    assert i == s.index_next_attestation_duty_to_be_served;
                    assert s.sequence_attestation_duties_to_be_served[i].node == event.node;
                    assert i == s'.index_next_attestation_duty_to_be_served - 1;
                    assert s'.sequence_attestation_duties_to_be_served[i].node == event.node;
                    assert false;
                }
            }
        }       
    }       


    lemma lem_inv_attestation_duty_queue_is_ordered_4(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires 
        && inv_attestation_duty_queue_is_ordered_3(s) //  
        && inv_attestation_duty_queue_is_ordered_4(s) //    
        && is_sequence_attestation_duties_to_be_served_orderd(s) //    
    ensures inv_attestation_duty_queue_is_ordered_4(s');  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                lem_inv_attestation_duty_queue_is_ordered_4_honest(s, event, s');
                   
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_attestation_duty_queue_is_ordered_4_body_body(s', hn, s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_3(s, event, s', s.honest_nodes_states[hn], hn);
                        if event.event.ServeAttstationDuty?
                        {
                            lem_inv_attestation_duty_queue_is_ordered_4_helper_other_node(
                                s,
                                event,
                                s',
                                hn
                            );
                        }
                        else
                        {
                            assert inv_attestation_duty_queue_is_ordered_4_body_body(s', hn, s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served);    
                        }
                        
                    }
                }  
                         
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_attestation_duty_queue_is_ordered_4_body_body(s', hn, s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served); 
                {
                    assert s'.index_next_attestation_duty_to_be_served == s.index_next_attestation_duty_to_be_served;
                    lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_3(s, event, s', s.honest_nodes_states[hn], hn);
                    lemma2_inv_attestation_duty_queue_is_ordered_4_body_body(s', hn, s.honest_nodes_states[hn], s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served);
                }  

        }
    }    

    lemma lem_inv_g_a_iii_f_serve_attestation_duty(
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
    requires inv_g_a_iii_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, process)
    requires inv_g_d_a_body_body(dv, n, process)
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)  
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process)  
    requires is_sequence_attestation_duties_to_be_served_orderd(dv);
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)
    requires inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, process)
    requires inv_g_a_iv_a_body_body(dv, n, process)    
    requires lem_ServeAttstationDuty2_predicate(dv, index_next_attestation_duty_to_be_served, attestation_duty, n)
    ensures inv_g_a_iii_body_body(dv, n, s', index_next_attestation_duty_to_be_served);
    {
        var new_p := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
        );

        if |process.attestation_duties_queue| == 0 
        {
            assert inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, new_p);  
        }
        else 
        {
            forall i: nat, k, l, t  |
                inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                    dv,
                    n, 
                    new_p,
                    i,
                    k, 
                    l, 
                    t
                )
            ensures 
                new_p.attestation_duties_queue[i-1].slot == dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot      
            {
                // assert process.attestation_duties_queue != [];
                assert i > 0;


                if i != |new_p.attestation_duties_queue| - 1
                {
                    assert inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                        dv,
                        n, 
                        process,
                        i,
                        k, 
                        l, 
                        t                        
                    );
                }
                else 
                {
                    assert new_p.attestation_duties_queue[i-1] == process.attestation_duties_queue[|process.attestation_duties_queue|-1];

                    assert l == index_next_attestation_duty_to_be_served-1;

                    assert new_p.attestation_duties_queue[i-1].slot <= dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;

                    assert inv_attestation_duty_queue_is_ordered_4_body_body_premise(dv, n, process, t, index_next_attestation_duty_to_be_served-1);

                    assert new_p.attestation_duties_queue[i-1].slot == dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;
                }

            }   
        }



        lem_inv_g_a_iii_f_check_for_next_queued_duty(new_p, s', dv, n, index_next_attestation_duty_to_be_served);
    } 

    lemma lem_inv_inv_decided_values_of_previous_duties_are_known_body_body_new_intermediate_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s_mod: DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )  
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process)   
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)    
    requires dv.consensus_on_attestation_data[id].decided_value.isPresent()
    requires dv.consensus_on_attestation_data[id].decided_value.safe_get() ==  decided_attestation_data 
    requires process.current_attestation_duty.isPresent()
    requires id == process.current_attestation_duty.safe_get().slot;        
    requires 
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
            s_mod ==
            process.(
                current_attestation_duty := None,
                attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                attestation_slashing_db := attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    process.attestation_consensus_engine_state,
                    attestation_slashing_db
                )
            );
    ensures inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, s_mod);
    {

        assert s_mod.attestation_duties_queue == process.attestation_duties_queue;

        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process, s_mod);

        assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, s_mod);
    }

    lemma lem_inv_inv_decided_values_of_previous_duties_are_known_body_body_new_intermediate_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,        
        s_mod: DVCState,
        dv: DVState,
        n: BLSPubkey
    )  
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, process)
    requires inv_g_d_a_body_body(dv, n, process)
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)
    requires concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv)
    requires pred_data_of_att_share_is_decided_value(dv)         
    requires pred_axiom_is_my_attestation_2(dv, process, block)
    requires 
            var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

            var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

            var future_att_consensus_instances_already_decided := 
                f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided); 

            var new_process :=
                process.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys
                ); 

            && new_process.current_attestation_duty.isPresent() && new_process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided  

            && var decided_attestation_data := att_consensus_instances_already_decided[new_process.current_attestation_duty.safe_get().slot];

            var new_attestation_slashing_db := f_update_attestation_slashing_db(new_process.attestation_slashing_db, decided_attestation_data);                                  
                                

 
            && s_mod ==
                new_process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    new_process.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            )
    ensures inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, s_mod);
    {
            var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

            var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

            var future_att_consensus_instances_already_decided := 
                f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided); 

            var new_process :=
                process.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys
                ); 

            var decided_attestation_data := att_consensus_instances_already_decided[new_process.current_attestation_duty.safe_get().slot];
            
            var new_attestation_slashing_db := f_update_attestation_slashing_db(new_process.attestation_slashing_db, decided_attestation_data);         

            // lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process, s_mod);


            lem_f_listen_for_new_imported_blocks_helper_1(
                dv,
                process,
                block,
                new_consensus_instances_already_decided
            );

            assert 
                && dv.consensus_on_attestation_data[new_process.current_attestation_duty.safe_get().slot].decided_value.isPresent()
                && dv.consensus_on_attestation_data[new_process.current_attestation_duty.safe_get().slot].decided_value.safe_get() == decided_attestation_data
            ;                        

            assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, s_mod);

    }    

    lemma lem_inv_g_a_iii_f_att_consensus_decided(
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
    requires inv_g_a_iii_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, process)
    requires inv_g_d_a_body_body(dv, n, process)
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dv, n, process, index_next_attestation_duty_to_be_served)  
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process)  


    requires inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, process)
    requires inv_g_a_iv_a_body_body(dv, n, process)
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)

    requires dv.consensus_on_attestation_data[id].decided_value.isPresent()
    requires dv.consensus_on_attestation_data[id].decided_value.safe_get() ==  decided_attestation_data 
    ensures inv_g_a_iii_body_body(dv, n, s', index_next_attestation_duty_to_be_served)
    {     
        if  && process.current_attestation_duty.isPresent()
            && id == process.current_attestation_duty.safe_get().slot
        {
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

            assert s_mod.attestation_duties_queue == process.attestation_duties_queue;

            lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process, s_mod);

            lem_inv_inv_decided_values_of_previous_duties_are_known_body_body_new_intermediate_f_att_consensus_decided(process, id, decided_attestation_data, s_mod, dv, n, index_next_attestation_duty_to_be_served);

            assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, s_mod);

            assert get_upperlimit_decided_instances(s_mod) == process.latest_attestation_duty.safe_get().slot + 1;

            if
                &&  |s_mod.attestation_duties_queue| > 0 
                &&   !s_mod.current_attestation_duty.isPresent()        
            {
                forall an |
                    && an in dv.sequence_attestation_duties_to_be_served.Values 
                    && an.node == n 
                    && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot   
                ensures      
                        var slot := an.attestation_duty.slot;
                            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                        
                {
                    var slot := an.attestation_duty.slot;

                    if slot > s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                    
                    }
                    else if slot == s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                         
                    }
                    else 
                    {
                        assert slot < s_mod.latest_attestation_duty.safe_get().slot;
                        assert 
                            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                           
                    }

                }
            }
            assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, s_mod);

            assert inv_g_a_iii_body_body(dv, n, s_mod, index_next_attestation_duty_to_be_served);        


            lem_inv_g_a_iii_f_check_for_next_queued_duty(s_mod, s', dv, n, index_next_attestation_duty_to_be_served);     
        }        
    }      

    lemma lem_inv_g_a_iii_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        s': DVCState,
        dv': DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires inv_g_a_iii_body_body(dv', n, process, index_next_attestation_duty_to_be_served)
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv', n, process)
    requires inv_g_d_a_body_body(dv', n, process)
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dv', n, process, index_next_attestation_duty_to_be_served)  
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv', n, process, index_next_attestation_duty_to_be_served)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv', n, process)
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)
    requires inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv', n, process)
    requires inv_g_a_iv_a_body_body(dv', n, process)
    requires concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv')
    requires pred_data_of_att_share_is_decided_value(dv')  
    requires pred_axiom_is_my_attestation_2(dv', process, block)
    ensures inv_g_a_iii_body_body(dv', n, s', index_next_attestation_duty_to_be_served)
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var new_process :=
                process.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );                     

        if new_process.current_attestation_duty.isPresent() && new_process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            // Stop(current_attestation_duty.safe_get().slot);
            var decided_attestation_data := att_consensus_instances_already_decided[new_process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(new_process.attestation_slashing_db, decided_attestation_data);
            var s_mod := new_process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    new_process.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );

            lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dv', n, process, s_mod);

            lem_f_listen_for_new_imported_blocks_helper_1(
                dv',
                process,
                block,
                new_consensus_instances_already_decided
            );

            assert inv_g_d_a_body_body(dv', n, s_mod);    

            lem_inv_inv_decided_values_of_previous_duties_are_known_body_body_new_intermediate_f_listen_for_new_imported_blocks(
                process, block, s_mod, dv', n
            );

            assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv', n, s_mod);


            if
                &&  |s_mod.attestation_duties_queue| > 0 
                &&   !s_mod.current_attestation_duty.isPresent()        
            {
                forall an |
                    && an in dv'.sequence_attestation_duties_to_be_served.Values 
                    && an.node == n 
                    && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot   
                ensures      
                        var slot := an.attestation_duty.slot;
                            && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                        
                {
                    var slot := an.attestation_duty.slot;

                    if slot > s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                    
                    }
                    else if slot == s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                         
                    }
                    else 
                    {
                        assert slot < s_mod.latest_attestation_duty.safe_get().slot;
                        assert 
                            && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                           
                    }

                }
            }
            assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv', n, s_mod);                 
                   
            lem_inv_g_a_iii_f_check_for_next_queued_duty(s_mod, s', dv', n, index_next_attestation_duty_to_be_served);                    
        }        
    }           


    lemma lem_inv_g_a_iii_f_check_for_next_queued_duty(
        process: DVCState,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state  
    requires inv_g_a_iii_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, process)
    requires inv_g_d_a_body_body(dv, n, process)
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dv, n, process, index_next_attestation_duty_to_be_served)  
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process)

    requires pred_inv_current_latest_attestation_duty_match_body_body(process)
    requires inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, process)
    requires inv_g_a_iv_a_body_body(dv, n, process)

    ensures inv_g_a_iii_body_body(dv, n, s', index_next_attestation_duty_to_be_served)
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
                             

                if
                    &&  |s_mod.attestation_duties_queue| == 0 
                {
                    assert process.attestation_duties_queue == [queue_head];
                    // assert !process.current_attestation_duty.isPresent()
                    forall i:nat  |
                        && i < index_next_attestation_duty_to_be_served
                        && var an := dv.sequence_attestation_duties_to_be_served[i];
                        && an.node == n 
                        && inv_g_a_iii_body_body_helper(s_mod, an.attestation_duty.slot)
                    ensures 
                        var an := dv.sequence_attestation_duties_to_be_served[i];
                        var slot := an.attestation_duty.slot;   
                        && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db      
                        ;                                           
                    {
                        var an := dv.sequence_attestation_duties_to_be_served[i];
                        var slot := an.attestation_duty.slot;

                        if slot < queue_head.slot 
                        {
                            if  !process.current_attestation_duty.isPresent()
                            {
                                assert
                                && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                                && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db      
                                ; 
                            }
                            else 
                            {
                                if slot != process.current_attestation_duty.safe_get().slot
                                {
                                    assert get_upperlimit_decided_instances(process) == process.latest_attestation_duty.safe_get().slot;

                                    if slot < process.latest_attestation_duty.safe_get().slot
                                    {
                                        assert
                                        && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                                        && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db      
                                        ;                                             
                                    }
                                    else 
                                    {
                                        assert slot > process.latest_attestation_duty.safe_get().slot;
                                        assert
                                        && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                                        && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db      
                                        ;                                           
                                    }                                  
                                }
                                else 
                                {
                                    assert false;
                                }
                            }
                        }
                        else 
                        {
                            assert slot >= queue_head.slot;

                            assert
                            inv_attestation_duty_queue_is_ordered_4_body_body_premise(
                                dv,
                                n, 
                                process,
                                i,
                                index_next_attestation_duty_to_be_served
                            );                            

                            var last := seq_last(process.attestation_duties_queue);
                            assert last.slot == dv.sequence_attestation_duties_to_be_served[i].attestation_duty.slot;

                            assert
                            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && process.future_att_consensus_instances_already_decided[slot] == dv.consensus_on_attestation_data[slot].decided_value.safe_get()  
                            ;               

                            assert 
                            && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db   
                            ;                                       
                            // assert last.slot == queue_head.slot;

                        }

              
                    }
                }
                assert inv_g_a_iii_body_body(dv, n, s_mod, index_next_attestation_duty_to_be_served);

                if  && |s_mod.attestation_duties_queue| > 0 
                    &&   !s_mod.current_attestation_duty.isPresent()
                {
                  
                    forall an |
                        && an in dv.sequence_attestation_duties_to_be_served.Values 
                        && an.node == n 
                        && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot
                    ensures 
                        var slot := an.attestation_duty.slot;
                        && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                    ;                          
                    {
                        var slot := an.attestation_duty.slot;
                   
                        if an.attestation_duty.slot < process.attestation_duties_queue[0].slot  
                        {
                            assert 
                                && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                                && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                            ;
                        }
                        else 
                        {
                            var t :|  dv.sequence_attestation_duties_to_be_served[t] == an;
                            assert process.attestation_duties_queue[0] in process.attestation_duties_queue;
                            var i :|  
                                    && dv.sequence_attestation_duties_to_be_served[i].node == n 
                                    && dv.sequence_attestation_duties_to_be_served[i].attestation_duty == process.attestation_duties_queue[0];
                            assert process.attestation_duties_queue[1] in process.attestation_duties_queue;
                            var j :|  
                                    && dv.sequence_attestation_duties_to_be_served[j].node == n 
                                    && dv.sequence_attestation_duties_to_be_served[j].attestation_duty == process.attestation_duties_queue[1];   

                            lem_inv_attestation_duty_queue_is_ordered_3_body_body(
                                dv,
                                n,
                                process,
                                1,
                                i,
                                j,
                                t
                            ); 

                        
                            assert 
                                && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                                && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                            ;
                            
                        }
                    }                  
                }
                assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(dv, n, s_mod);     

                forall ad  |
                    && ad in s_mod.attestation_duties_queue
                ensures ad in process.attestation_duties_queue
                {
                    var i :| 0 <= i < |s_mod.attestation_duties_queue|
                                && s_mod.attestation_duties_queue[i] == ad;
                    assert ad in process.attestation_duties_queue;
                }          

                if 
                    &&  |s_mod.attestation_duties_queue| > 0 
                    &&   s_mod.latest_attestation_duty.isPresent()     
                {
                    assert 
                        &&  |process.attestation_duties_queue| > 0 
                        &&   process.latest_attestation_duty.isPresent()  
                    ;

                    forall an |
                        && an in dv.sequence_attestation_duties_to_be_served.Values 
                        && an.node == n 
                        && s_mod.latest_attestation_duty.safe_get().slot < an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot   
                    ensures 
                        var slot := an.attestation_duty.slot;
                        && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db                          
                    {
                        var slot := an.attestation_duty.slot;

                        assert process.latest_attestation_duty.safe_get().slot < an.attestation_duty.slot;

                        if slot < process.attestation_duties_queue[0].slot
                        {

                        }
                        else 
                        {
                            var t :|  dv.sequence_attestation_duties_to_be_served[t] == an;
                            assert process.attestation_duties_queue[0] in process.attestation_duties_queue;
                            var k :|  
                                    && dv.sequence_attestation_duties_to_be_served[k].node == n 
                                    && dv.sequence_attestation_duties_to_be_served[k].attestation_duty == process.attestation_duties_queue[0];
                            assert process.attestation_duties_queue[1] in process.attestation_duties_queue;
                            var l :|  
                                    && dv.sequence_attestation_duties_to_be_served[l].node == n 
                                    && dv.sequence_attestation_duties_to_be_served[l].attestation_duty == process.attestation_duties_queue[1];   

                            lem_inv_attestation_duty_queue_is_ordered_3_body_body(
                                dv,
                                n,
                                process,
                                1,
                                k,
                                l,
                                t
                            ); 

                        
                            assert 
                                && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                                && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                            ;
                            
                        }
                    }               
                }  
                assert inv_g_a_iv_a_body_body(dv, n, s_mod);         


                lemma3_inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process, s_mod);


                lem_inv_g_a_iii_f_check_for_next_queued_duty(s_mod, s', dv, n , index_next_attestation_duty_to_be_served);
            }
            else 
            {
                var new_process := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..]
                );          

                assert inv_g_a_iii_body_body(dv, n, s', index_next_attestation_duty_to_be_served);

            }
        } 
        else 
        {
            // assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, s');
        }       
    }  

    lemma lem_inv_g_a_iii_helper_easy(
        s: DVState,
        event: DV.Event,
        s_node: DVCState,
        s'_node: DVCState,
        n: BLSPubkey
    )
    requires inv_g_a_iii_body_body(s, n, s_node, s.index_next_attestation_duty_to_be_served)
    requires s_node.attestation_duties_queue == s'_node.attestation_duties_queue
    requires s_node.current_attestation_duty == s'_node.current_attestation_duty
    requires s_node.attestation_slashing_db <= s'_node.attestation_slashing_db
    ensures inv_g_a_iii_body_body(s, n, s'_node, s.index_next_attestation_duty_to_be_served)        
    {
          
  
        
    }      

    lemma lem_inv_g_a_iii_helper_honest_ServeAttestationDuty(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s)
    requires event.HonestNodeTakingStep?
    requires event.event.ServeAttstationDuty?
    ensures inv_g_a_iii_body_body(s', event.node, s'.honest_nodes_states[event.node], s'.index_next_attestation_duty_to_be_served); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3a(s, event, s', s_node, node);
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3c(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_1(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_2(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_3(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_4(s, event, s', s_node, node);

                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_multiple(s, event, s', s_node, node);

                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s, event, s');
                lem_pred_data_of_att_share_is_decided_value(s, event, s');

                lem_inv_sequence_attestation_duties_to_be_served_orderd(s, event, s');

                assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s', node, s_node);
                assert inv_g_d_a_body_body(s', node, s_node);
                assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(s', node, s_node);
                assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_g_a_iii_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node);
                assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');
                assert pred_data_of_att_share_is_decided_value(s');             
                assert inv_g_a_iv_a_body_body(s', node, s_node);
                assert is_sequence_attestation_duties_to_be_served_orderd(s');

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        // assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lem_ServeAttstationDuty2(s, event, s');
                        lem_inv_g_a_iii_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_g_a_iii_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);
                }
        }
    }

    lemma lem_inv_g_a_iii_helper_honest(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s)
    requires event.HonestNodeTakingStep?
    ensures inv_g_a_iii_body_body(s', event.node, s'.honest_nodes_states[event.node], s'.index_next_attestation_duty_to_be_served); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3a(s, event, s', s_node, node);
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3c(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_1(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_2(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_3(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_4(s, event, s', s_node, node);

                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_multiple(s, event, s', s_node, node);

                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s, event, s');
                lem_pred_data_of_att_share_is_decided_value(s, event, s');

                lem_inv_sequence_attestation_duties_to_be_served_orderd(s, event, s');

                assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s', node, s_node);
                assert inv_g_d_a_body_body(s', node, s_node);
                assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(s', node, s_node);
                assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_g_a_iii_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node);
                assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');
                assert pred_data_of_att_share_is_decided_value(s');             
                assert inv_g_a_iv_a_body_body(s', node, s_node);
                assert is_sequence_attestation_duties_to_be_served_orderd(s');

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        lem_inv_g_a_iii_helper_honest_ServeAttestationDuty(s, event, s');
                        assert inv_g_a_iii_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        lem_NonServeAttstationDuty(s, event, s');
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper5(s, event, s');                 
                        lem_inv_g_a_iii_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_g_a_iii_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);    
               
                   
                    case ReceivedAttestationShare(attestation_share) =>
                        lem_NonServeAttstationDuty(s, event, s'); 
                        lem_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        lem_inv_g_a_iii_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_a_iii_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  
                        

                    case ImportedNewBlock(block) => 
                        lem_NonServeAttstationDuty(s, event, s');
                        var s_node2 := add_block_to_bn(s_node, nodeEvent.block);
                        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node, s_node2);
                        lemma2_inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s_node2, s.index_next_attestation_duty_to_be_served);
                        lem_inv_g_a_iii_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_g_a_iii_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                     
                    
                 
                    case ResendAttestationShares => 
                        lem_NonServeAttstationDuty(s, event, s');
                        lem_f_resend_attestation_share_constants(s_node, s'_node);
                        lem_inv_g_a_iii_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_a_iii_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  

                    case NoEvent => 
                        lem_NonServeAttstationDuty(s, event, s');
                        assert s_node == s'_node; 
                        lem_inv_g_a_iii_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_a_iii_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                          
                }
                // assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  
        }
    }   

    lemma lem_inv_g_a_iii_helper_other_node(
        s: DVState,
        event: DV.Event,
        s': DVState,
        hn: BLSPubkey
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires 
        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s)    
    requires event.HonestNodeTakingStep?
    requires event.event.ServeAttstationDuty?
    requires event.node != hn 
    requires hn in s.honest_nodes_states
    ensures inv_g_a_iii_body_body(s', hn, s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served)
    {
        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_2(s, event, s', s.honest_nodes_states[hn], hn);

        assert s'.index_next_attestation_duty_to_be_served == s.index_next_attestation_duty_to_be_served + 1;

        assert s.sequence_attestation_duties_to_be_served[s.index_next_attestation_duty_to_be_served].node == event.node;

        var s_nodeh := s.honest_nodes_states[hn];
        var s'_nodeh := s'.honest_nodes_states[hn];

        assert inv_attestation_duty_queue_is_ordered_4_body_body(s', hn, s_nodeh, s.index_next_attestation_duty_to_be_served);

        if |s'_nodeh.attestation_duties_queue| == 0
        {
            assert |s_nodeh.attestation_duties_queue| == 0;

            forall i:nat  |
                && i < s'.index_next_attestation_duty_to_be_served
                && var an := s'.sequence_attestation_duties_to_be_served[i];
                && an.node == hn 
                && inv_g_a_iii_body_body_helper(s'_nodeh, an.attestation_duty.slot)
            ensures
                && var an := s'.sequence_attestation_duties_to_be_served[i];
                var slot := an.attestation_duty.slot;
                && s'.consensus_on_attestation_data[slot].decided_value.isPresent()
                && construct_SlashingDBAttestation_from_att_data(s'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s'_nodeh.attestation_slashing_db
            {
                var an := s'.sequence_attestation_duties_to_be_served[i];
                var slot := an.attestation_duty.slot;

                if i < s.index_next_attestation_duty_to_be_served
                {
                    assert 
                        && s'.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(s'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s'_nodeh.attestation_slashing_db
                    ;
                }
                else 
                {
                    assert i == s.index_next_attestation_duty_to_be_served;
                    assert s.sequence_attestation_duties_to_be_served[i].node == event.node;
                    assert i == s'.index_next_attestation_duty_to_be_served - 1;
                    assert s'.sequence_attestation_duties_to_be_served[i].node == event.node;
                    assert false;
                }
            }
        }       
    }           

    lemma lem_inv_g_a_iii(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s)
    ensures inv_g_a_iii(s');  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_g_a_iii_helper_honest(s, event, s');
                   
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_g_a_iii_body_body(s', hn, s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_2(s, event, s', s.honest_nodes_states[hn], hn);
                        if event.event.ServeAttstationDuty?
                        {
                            lem_inv_g_a_iii_helper_other_node(
                                s,
                                event,
                                s',
                                hn
                            );
                        }
                        else
                        {   
                            lem_inv_g_a_iii_helper_easy(s', event, s.honest_nodes_states[hn], s'.honest_nodes_states[hn], hn);                            
                        }                        

                    }
                }  

                         
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_g_a_iii_body_body(s', hn, s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_2(s, event, s', s.honest_nodes_states[hn], hn);
                        lem_inv_g_a_iii_helper_easy(s', event, s.honest_nodes_states[hn], s'.honest_nodes_states[hn], hn);                                                                    
                    }
                }              
 

        }
    }         
    
    
    lemma lem_inv_g_a_iv_a_f_serve_attestation_duty(
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
    requires inv_g_a_iv_a_body_body(dv, n, process)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process)
    requires inv_g_d_a_body_body(dv, n, process)

    requires inv_g_a_iii_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)  
    requires is_sequence_attestation_duties_to_be_served_orderd(dv);
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)

    requires lem_ServeAttstationDuty2_predicate(dv, index_next_attestation_duty_to_be_served, attestation_duty, n)
    ensures inv_g_a_iv_a_body_body(dv, n, s') 
    {
        var new_p := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
        );

        if |process.attestation_duties_queue| == 0 
        {
            assert inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, new_p);  
        }
        else 
        {
            forall i: nat, k, l, t  |
                inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                    dv,
                    n, 
                    new_p,
                    i,
                    k, 
                    l, 
                    t
                )
            ensures 
                new_p.attestation_duties_queue[i-1].slot == dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot      
            {
                // assert process.attestation_duties_queue != [];
                assert i > 0;


                if i != |new_p.attestation_duties_queue| - 1
                {
                    assert inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                        dv,
                        n, 
                        process,
                        i,
                        k, 
                        l, 
                        t                        
                    );
                }
                else 
                {
                    assert new_p.attestation_duties_queue[i-1] == process.attestation_duties_queue[|process.attestation_duties_queue|-1];

                    assert l == index_next_attestation_duty_to_be_served-1;

                    assert new_p.attestation_duties_queue[i-1].slot <= dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;

                    assert inv_attestation_duty_queue_is_ordered_4_body_body_premise(dv, n, process, t, index_next_attestation_duty_to_be_served-1);

                    assert new_p.attestation_duties_queue[i-1].slot == dv.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;
                }

            }   
        }

        lem_inv_g_a_iv_f_check_for_next_queued_duty(new_p, s', dv, n, index_next_attestation_duty_to_be_served);
    }          

    lemma lem_inv_g_a_iv_a_f_att_consensus_decided(
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
    requires inv_g_a_iv_a_body_body(dv, n, process)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process)
    requires inv_g_d_a_body_body(dv, n, process)

    requires dv.consensus_on_attestation_data[id].decided_value.isPresent()
    requires dv.consensus_on_attestation_data[id].decided_value.safe_get() ==  decided_attestation_data 
    ensures inv_g_a_iv_a_body_body(dv, n, s')       
    {     
        if  && process.current_attestation_duty.isPresent()
            && id == process.current_attestation_duty.safe_get().slot
        {
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

            lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process, s_mod);

            lem_inv_g_a_iv_f_check_for_next_queued_duty(s_mod, s', dv, n, index_next_attestation_duty_to_be_served);    
        }         
    }        

    lemma lem_inv_g_a_iv_a_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        s': DVCState,
        dv': DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_g_a_iv_a_body_body(dv', n, process)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv', n, process, index_next_attestation_duty_to_be_served)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv', n, process)
    requires inv_g_d_a_body_body(dv', n, process)
    requires concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv')
    requires pred_data_of_att_share_is_decided_value(dv') 
    requires pred_axiom_is_my_attestation_2(dv', process, block)
    ensures inv_g_a_iv_a_body_body(dv', n, s')   
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var new_process :=
                process.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );                     

        if new_process.current_attestation_duty.isPresent() && new_process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            // Stop(current_attestation_duty.safe_get().slot);
            var decided_attestation_data := att_consensus_instances_already_decided[new_process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(new_process.attestation_slashing_db, decided_attestation_data);
            var s_mod := new_process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    new_process.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );

            lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dv', n, process, s_mod);

            lem_f_listen_for_new_imported_blocks_helper_1(
                dv',
                process,
                block,
                new_consensus_instances_already_decided
            );

            assert inv_g_d_a_body_body(dv', n, s_mod);    
                   
            lem_inv_g_a_iv_f_check_for_next_queued_duty(s_mod, s', dv', n, index_next_attestation_duty_to_be_served);                    
        }        
    }        


    lemma lem_inv_g_a_iv_f_check_for_next_queued_duty(
        process: DVCState,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state  
    requires inv_g_a_iv_a_body_body(dv, n, process)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process)
    requires inv_g_d_a_body_body(dv, n, process)
    ensures inv_g_a_iv_a_body_body(dv, n, s')
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
                             
 
                forall ad  |
                    && ad in s_mod.attestation_duties_queue
                ensures ad in process.attestation_duties_queue
                {
                    var i :| 0 <= i < |s_mod.attestation_duties_queue|
                                && s_mod.attestation_duties_queue[i] == ad;
                    assert ad in process.attestation_duties_queue;
                }          

                if 
                    &&  |s_mod.attestation_duties_queue| > 0 
                    &&   s_mod.latest_attestation_duty.isPresent()     
                {
                    assert 
                        &&  |process.attestation_duties_queue| > 0 
                        &&   process.latest_attestation_duty.isPresent()  
                    ;

                    forall an |
                        && an in dv.sequence_attestation_duties_to_be_served.Values 
                        && an.node == n 
                        && s_mod.latest_attestation_duty.safe_get().slot < an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot   
                    ensures 
                        var slot := an.attestation_duty.slot;
                        && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db                          
                    {
                        var slot := an.attestation_duty.slot;

                        assert process.latest_attestation_duty.safe_get().slot < an.attestation_duty.slot;

                        if slot < process.attestation_duties_queue[0].slot
                        {

                        }
                        else 
                        {
                            var t :|  dv.sequence_attestation_duties_to_be_served[t] == an;
                            assert process.attestation_duties_queue[0] in process.attestation_duties_queue;
                            var k :|  
                                    && dv.sequence_attestation_duties_to_be_served[k].node == n 
                                    && dv.sequence_attestation_duties_to_be_served[k].attestation_duty == process.attestation_duties_queue[0];
                            assert process.attestation_duties_queue[1] in process.attestation_duties_queue;
                            var l :|  
                                    && dv.sequence_attestation_duties_to_be_served[l].node == n 
                                    && dv.sequence_attestation_duties_to_be_served[l].attestation_duty == process.attestation_duties_queue[1];   

                            lem_inv_attestation_duty_queue_is_ordered_3_body_body(
                                dv,
                                n,
                                process,
                                1,
                                k,
                                l,
                                t
                            ); 

                        
                            assert 
                                && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                                && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                            ;
                            
                        }
                    }               
                }  
                assert inv_g_a_iv_a_body_body(dv, n, s_mod);         


                lemma3_inv_attestation_duty_queue_is_ordered_3_body_body(dv, n, process, s_mod);


                lem_inv_g_a_iv_f_check_for_next_queued_duty(s_mod, s', dv, n , index_next_attestation_duty_to_be_served);
            }
            else 
            {
                var new_process := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..]
                );          

                if 
                    &&  |s'.attestation_duties_queue| > 0 
                    &&  s'.latest_attestation_duty.isPresent()     
                {
                    assert |process.attestation_duties_queue| > 0;

                    forall an |
                        && an in dv.sequence_attestation_duties_to_be_served.Values 
                        && an.node == n 
                        && s'.latest_attestation_duty.safe_get().slot < an.attestation_duty.slot < s'.attestation_duties_queue[0].slot 
                    ensures
                        var slot := an.attestation_duty.slot;
                        && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s'.attestation_slashing_db     
                            ;   
                    {
                        if process.latest_attestation_duty.isPresent()   
                        {
                            var slot := an.attestation_duty.slot;

                            // assert process.latest_attestation_duty.safe_get().slot < an.attestation_duty.slot;

                            if slot < process.attestation_duties_queue[0].slot
                            {

                            }
                            else 
                            {
                                var t :|  dv.sequence_attestation_duties_to_be_served[t] == an;
                                assert process.attestation_duties_queue[0] in process.attestation_duties_queue;
                                var k :|  
                                        && dv.sequence_attestation_duties_to_be_served[k].node == n 
                                        && dv.sequence_attestation_duties_to_be_served[k].attestation_duty == process.attestation_duties_queue[0];
                                assert process.attestation_duties_queue[1] in process.attestation_duties_queue;
                                var l :|  
                                        && dv.sequence_attestation_duties_to_be_served[l].node == n 
                                        && dv.sequence_attestation_duties_to_be_served[l].attestation_duty == process.attestation_duties_queue[1];   

                                lem_inv_attestation_duty_queue_is_ordered_3_body_body(
                                    dv,
                                    n,
                                    process,
                                    1,
                                    k,
                                    l,
                                    t
                                ); 

                            
                                assert 
                                    && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                                    && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s'.attestation_slashing_db     
                                ;
                                
                            }    
                            assert 
                                && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                                && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s'.attestation_slashing_db     
                            ;                                                    
                        }  
                        else 
                        {
                            var slot := an.attestation_duty.slot;
                            if slot < process.attestation_duties_queue[0].slot
                            {

                            }
                            else 
                            {
                                var t :|  dv.sequence_attestation_duties_to_be_served[t] == an;
                                assert process.attestation_duties_queue[0] in process.attestation_duties_queue;
                                var k :|  
                                        && dv.sequence_attestation_duties_to_be_served[k].node == n 
                                        && dv.sequence_attestation_duties_to_be_served[k].attestation_duty == process.attestation_duties_queue[0];
                                assert process.attestation_duties_queue[1] in process.attestation_duties_queue;
                                var l :|  
                                        && dv.sequence_attestation_duties_to_be_served[l].node == n 
                                        && dv.sequence_attestation_duties_to_be_served[l].attestation_duty == process.attestation_duties_queue[1];   

                                lem_inv_attestation_duty_queue_is_ordered_3_body_body(
                                    dv,
                                    n,
                                    process,
                                    1,
                                    k,
                                    l,
                                    t
                                ); 

                            
                                assert 
                                    && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                                    && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s'.attestation_slashing_db     
                                ;
                                
                            }    
                            assert 
                                && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                                && construct_SlashingDBAttestation_from_att_data(dv.consensus_on_attestation_data[slot].decided_value.safe_get()) in s'.attestation_slashing_db     
                            ;                               
                        }
                    }
                }  

                assert inv_g_a_iv_a_body_body(dv, n, s');         

            }
        } 
        else 
        {
            // assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, s');
        }       
    }  

    lemma lem_inv_g_a_iv_a_helper_honest_ServeAttestationDuty(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s)
    requires event.HonestNodeTakingStep?
    requires event.event.ServeAttstationDuty?
    ensures inv_g_a_iv_a_body_body(s', event.node, s'.honest_nodes_states[event.node]); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        var s_node := s.honest_nodes_states[event.node];
        var s'_node := s'.honest_nodes_states[event.node];        
        match event 
        {
            
            case HonestNodeTakingStep(_, nodeEvent, nodeOutputs) =>
                // NOTE: No idea why if one just uses `node` rathern than `event.node` 
                // by listing node above in place of the underscore, Dafny cannot conclude
                // the lemma postcondition !!!
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3a(s, event, s', s_node, event.node);
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3c(s, event, s', s_node, event.node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_1(s, event, s', s_node, event.node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_2(s, event, s', s_node, event.node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_3(s, event, s', s_node, event.node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_4(s, event, s', s_node, event.node);

                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_multiple(s, event, s', s_node, event.node);

                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s, event, s');
                lem_pred_data_of_att_share_is_decided_value(s, event, s');

                lem_inv_sequence_attestation_duties_to_be_served_orderd(s, event, s');

                assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s', event.node, s_node);
                assert inv_g_d_a_body_body(s', event.node, s_node);
                assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(s', event.node, s_node);
                assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', event.node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_g_a_iii_body_body(s', event.node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_attestation_duty_queue_is_ordered_3_body_body(s', event.node, s_node);
                assert inv_attestation_duty_queue_is_ordered_4_body_body(s', event.node, s_node, s.index_next_attestation_duty_to_be_served);
                assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');
                assert pred_data_of_att_share_is_decided_value(s');             
                assert inv_g_a_iv_a_body_body(s', event.node, s_node);
                assert is_sequence_attestation_duties_to_be_served_orderd(s');

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        // assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lem_ServeAttstationDuty2(s, event, s');
                        lem_inv_g_a_iv_a_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            event.node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_g_a_iv_a_body_body(s', event.node, s'_node);
                }
                assert inv_g_a_iv_a_body_body(s', event.node, s'_node);
        }
    }    

    lemma lem_inv_g_a_iv_a_helper_easy(
        s: DVState,
        event: DV.Event,
        s_node: DVCState,
        s'_node: DVCState,
        n: BLSPubkey
    )
    requires inv_g_a_iv_a_body_body(s, n, s_node)
    requires s_node.attestation_duties_queue == s'_node.attestation_duties_queue
    requires s_node.latest_attestation_duty == s'_node.latest_attestation_duty
    requires s_node.attestation_slashing_db <= s'_node.attestation_slashing_db
    ensures inv_g_a_iv_a_body_body(s, n, s'_node)        
    {
          
  
        
    }    

    lemma lem_inv_g_a_iv_a_helper_honest(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s)
    requires event.HonestNodeTakingStep?
    ensures inv_g_a_iv_a_body_body(s', event.node, s'.honest_nodes_states[event.node]); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3a(s, event, s', s_node, node);
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3c(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_1(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_2(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_3(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_4(s, event, s', s_node, node);

                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_multiple(s, event, s', s_node, node);

                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s, event, s');
                lem_pred_data_of_att_share_is_decided_value(s, event, s');

                lem_inv_sequence_attestation_duties_to_be_served_orderd(s, event, s');

                assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s', node, s_node);
                assert inv_g_d_a_body_body(s', node, s_node);
                assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(s', node, s_node);
                assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_g_a_iii_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node);
                assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');
                assert pred_data_of_att_share_is_decided_value(s');             
                assert inv_g_a_iv_a_body_body(s', node, s_node);
                assert is_sequence_attestation_duties_to_be_served_orderd(s');

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        lem_inv_g_a_iv_a_helper_honest_ServeAttestationDuty(s, event, s');
                        assert inv_g_a_iv_a_body_body(s', node, s'_node);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        lem_NonServeAttstationDuty(s, event, s');
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper5(s, event, s');                 
                        lem_inv_g_a_iv_a_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_g_a_iv_a_body_body(s', node, s'_node);    
               
                   
                    case ReceivedAttestationShare(attestation_share) =>
                        lem_NonServeAttstationDuty(s, event, s'); 
                        lem_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        lem_inv_g_a_iv_a_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_a_iv_a_body_body(s', node, s'_node);  
                        

                    case ImportedNewBlock(block) => 
                        lem_NonServeAttstationDuty(s, event, s');
                        var s_node2 := add_block_to_bn(s_node, nodeEvent.block);
                        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node, s_node2);
                        lem_inv_g_a_iv_a_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_g_a_iv_a_body_body(s', node, s'_node);                     
                    
                 
                    case ResendAttestationShares => 
                        lem_NonServeAttstationDuty(s, event, s');
                        lem_f_resend_attestation_share_constants(s_node, s'_node);
                        lem_inv_g_a_iv_a_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_a_iv_a_body_body(s', node, s'_node);  

                    case NoEvent => 
                        lem_NonServeAttstationDuty(s, event, s');
                        assert s_node == s'_node; 
                        lem_inv_g_a_iv_a_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_a_iv_a_body_body(s', node, s'_node);                          
                }
                // assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  
        }
    }            

  

    lemma lem_inv_g_a_iv_a(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s)
    ensures inv_g_a_iv_a(s');  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_g_a_iv_a_helper_honest(s, event, s');
                   
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_g_a_iv_a_body_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_4(s, event, s', s.honest_nodes_states[hn], hn);

                        lem_inv_g_a_iv_a_helper_easy(s', event, s.honest_nodes_states[hn], s'.honest_nodes_states[hn], hn);                            
                        
                    }
                }  

                         
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_g_a_iv_a_body_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    // if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_4(s, event, s', s.honest_nodes_states[hn], hn);

                        lem_inv_g_a_iv_a_helper_easy(s', event, s.honest_nodes_states[hn], s'.honest_nodes_states[hn], hn);                            
                        
                    }
                }            
 

        }
    } 

    lemma lem_inv_g_d_b_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state   
    requires inv_g_d_b_body_body(dv, n, process)
    ensures inv_g_d_b_body_body(dv, n, s');
    {
        var new_p := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
        );

        lem_inv_g_d_b_f_check_for_next_queued_duty(new_p, s', dv, n);
    }   

    lemma lem_inv_g_d_b_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        s': DVCState,
        dv': DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires inv_g_d_b_body_body(dv', n, process)
    requires concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv')
    requires pred_data_of_att_share_is_decided_value(dv')
    requires pred_axiom_is_my_attestation_2(dv', process, block)
    ensures inv_g_d_b_body_body(dv', n, s');
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var new_process :=
                process.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );    

        lem_f_listen_for_new_imported_blocks_helper_1(
            dv',
            process,
            block,
            new_consensus_instances_already_decided
        );                                    

        if new_process.current_attestation_duty.isPresent() && new_process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            // Stop(current_attestation_duty.safe_get().slot);
            var decided_attestation_data := att_consensus_instances_already_decided[new_process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(new_process.attestation_slashing_db, decided_attestation_data);
            var s_mod := new_process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    new_process.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );
            
            lem_inv_g_d_b_f_check_for_next_queued_duty(s_mod, s', dv', n);   
        }      
    }         

    lemma lem_inv_g_d_b_f_att_consensus_decided(
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
    requires inv_g_d_b_body_body(dv, n, process)
    ensures inv_g_d_b_body_body(dv, n, s'); 
    { 
        if  && process.current_attestation_duty.isPresent()
            && id == process.current_attestation_duty.safe_get().slot
        {
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

            lem_inv_g_d_b_f_check_for_next_queued_duty(s_mod, s', dv, n);   
        }
    }           

    lemma lem_inv_g_d_b_f_check_for_next_queued_duty(
        process: DVCState,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state  
    requires inv_g_d_b_body_body(dv, n, process)
    ensures inv_g_d_b_body_body(dv, n, s')
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

                lem_inv_g_d_b_f_check_for_next_queued_duty(s_mod, s', dv, n );
            }
            else 
            {        
                assert inv_g_d_b_body_body(dv, n, s');
            }
        } 
        else 
        {
        }       
    }  


    lemma lem_inv_g_d_b_transpose(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCState,
        n: BLSPubkey
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')      

    requires inv_g_d_b_body_body(s, n, s_node)


    // ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(s', n, s_node, s.index_next_attestation_duty_to_be_served)
    // ensures inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s', n, s_node)
    // ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', n, s_node, s.index_next_attestation_duty_to_be_served)
    // ensures inv_queued_att_duties_are_from_dv_seq_of_att_duties_body_body(s', n, s_node, s.index_next_attestation_duty_to_be_served)    
    ensures inv_g_d_b_body_body(s', n, s_node)    


    // requires inv_db_of_validity_predicate_contains_all_previous_decided_values(s)
    // requires invNetwork(s)
    // requires inv_quorum_constraints(s)
    // requires inv_only_dv_construct_signed_attestation_signature(s)
    // requires inv_queued_att_duty_is_rcvd_duty3(s)  
    // ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(s', s_node)  
    {
        assert s'.index_next_attestation_duty_to_be_served <= s'.index_next_attestation_duty_to_be_served <= s'.index_next_attestation_duty_to_be_served + 1;


        
    }      

    lemma lem_inv_g_d_b_helper_honest(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')     
    requires inv_g_d_b(s)
    requires lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s)  
    requires event.HonestNodeTakingStep?
    ensures inv_g_d_b_body_body(s', event.node, s'.honest_nodes_states[event.node]); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_g_d_b_transpose(s, event, s', s_node, node);
                // lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3c(s, event, s', s_node, node);
                // lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper4(s, event, s', s_node, node);

                // lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_1(s, event, s', s_node, node);
                // lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_2(s, event, s', s_node, node);
                // lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_3(s, event, s', s_node, node);
                // lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_4(s, event, s', s_node, node);

                // lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_helper_transpose_to_new_s_multiple(s, event, s', s_node, node);

                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s, event, s');
                lem_pred_data_of_att_share_is_decided_value(s, event, s');

                // lem_inv_sequence_attestation_duties_to_be_served_orderd(s, event, s');

                // assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s', node, s_node);
                assert inv_g_d_b_body_body(s', node, s_node);
                // assert inv_exists_decided_value_for_every_duty_before_queued_duties_body_body(s', node, s_node);
                // assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                // assert inv_g_a_iii_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                // assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node);
                // assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');
                assert pred_data_of_att_share_is_decided_value(s');             
                // assert inv_g_a_iv_a_body_body(s', node, s_node);
                // assert is_sequence_attestation_duties_to_be_served_orderd(s');

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lem_ServeAttstationDuty2(s, event, s');
                        lem_inv_g_d_b_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node
                        );
                        assert inv_g_d_b_body_body(s', node, s'_node);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        lem_NonServeAttstationDuty(s, event, s');
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper5(s, event, s');                 
                        lem_inv_g_d_b_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_g_d_b_body_body(s', node, s'_node);                        
               
                   
                    case ReceivedAttestationShare(attestation_share) =>
                        lem_NonServeAttstationDuty(s, event, s'); 
                        lem_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        // lem_inv_g_d_b_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_d_b_body_body(s', node, s'_node);  
                        

                    case ImportedNewBlock(block) => 
                        lem_NonServeAttstationDuty(s, event, s');
                        var s_node2 := add_block_to_bn(s_node, nodeEvent.block);
                        lem_inv_g_d_b_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_g_d_b_body_body(s', node, s'_node);                     
                    
                 
                    case ResendAttestationShares => 
                        lem_NonServeAttstationDuty(s, event, s');
                        lem_f_resend_attestation_share_constants(s_node, s'_node);
                        // lem_inv_g_d_b_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_d_b_body_body(s', node, s'_node);  

                    case NoEvent => 
                        lem_NonServeAttstationDuty(s, event, s');
                        assert s_node == s'_node; 
                        // lem_inv_g_d_b_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_d_b_body_body(s', node, s'_node);                          
                }
                // assert inv_g_d_b_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  
        }
    }     

    lemma lem_inv_g_d_b(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_new_precond(s)
    ensures inv_g_d_b(s');  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_g_d_b_helper_honest(s, event, s');
                   
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_g_d_b_body_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_inv_g_d_b_transpose(s, event, s', s.honest_nodes_states[hn], hn);
                    }
                }  
                assert inv_g_d_b(s');
                         
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_g_d_b_body_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    // if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lem_inv_g_d_b_transpose(s, event, s', s.honest_nodes_states[hn], hn);
                    }
                }  
                assert inv_g_d_b(s');

        }
    }             

}