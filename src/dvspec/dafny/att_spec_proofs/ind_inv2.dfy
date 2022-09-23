include "../commons.dfy"
include "../att_spec_proofs/helper_sets_lemmas.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "dvn_next_inv.dfy"
include "ind_inv.dfy"

module Att_Ind_Inv_With_Empty_Initial_Attestation_Slashing_DB2
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV    
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Helper_Sets_Lemmas
    import opened DVN_Next_Inv
    import opened Att_Ind_Inv_With_Empty_Initial_Attestation_Slashing_DB

    lemma lemma_inv_attestation_duty_queue_is_ordered_3_body_body(
        dvn: DVState, 
        n: BLSPubkey,
        n_state: DVCNodeState,
        i: nat, 
        k: nat,
        l: nat, 
        t: nat        
    )
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, n_state)
    requires inv_attestation_duty_queue_is_ordered_3_body_body_premise(dvn, n, n_state, i, k, l, t)
    ensures n_state.attestation_duties_queue[i-1].slot == dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot
    {

    }

    lemma lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(
        dvn: DVState, 
        n: BLSPubkey,
        n_state: DVCNodeState,
        n'_state: DVCNodeState
    )
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n , n_state)
    requires n_state.attestation_duties_queue == n'_state.attestation_duties_queue
    ensures inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n , n'_state)
    {
        forall i: nat, k, l, t  |
            inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                dvn,
                n, 
                n'_state,
                i,
                k, 
                l, 
                t
            )
        ensures 
            n'_state.attestation_duties_queue[i-1].slot == dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot      
        {
            // assert process.attestation_duties_queue != [];
            assert i > 0;

            assert inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                dvn,
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
        dvn: DVState, 
        n: BLSPubkey,
        n_state: DVCNodeState,
        n'_state: DVCNodeState,
        index_next_attestation_duty_to_be_served: nat
    )
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n , n_state, index_next_attestation_duty_to_be_served)
    requires n_state.attestation_duties_queue == n'_state.attestation_duties_queue
    ensures inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n , n'_state, index_next_attestation_duty_to_be_served)
    {
        if |n_state.attestation_duties_queue| > 0
        {
            forall i: nat|
                inv_attestation_duty_queue_is_ordered_4_body_body_premise(
                    dvn,
                    n, 
                    n'_state,
                    i,
                    index_next_attestation_duty_to_be_served
                )
            ensures 
                var last := n_state.attestation_duties_queue[|n_state.attestation_duties_queue|-1];
                last.slot == dvn.sequence_attestation_duties_to_be_served[i].attestation_duty.slot         
        
            {

                assert inv_attestation_duty_queue_is_ordered_4_body_body_premise(
                    dvn,
                    n, 
                    n_state,
                    i,
                    index_next_attestation_duty_to_be_served                     
                );
            }  
        }
      
    }    

    lemma lemma3_inv_attestation_duty_queue_is_ordered_3_body_body(
        dvn: DVState, 
        n: BLSPubkey,
        n_state: DVCNodeState,
        n'_state: DVCNodeState
    )
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n , n_state)
    requires |n_state.attestation_duties_queue| > 0
    requires  n'_state.attestation_duties_queue == n_state.attestation_duties_queue[1..]
    ensures inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n , n'_state)
    {
        forall i: nat, k, l, t  |
            inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                dvn,
                n, 
                n'_state,
                i,
                k, 
                l, 
                t
            )
        ensures 
            n'_state.attestation_duties_queue[i-1].slot == dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot      
        {
            assert n_state.attestation_duties_queue != [];
            assert i > 0;
            lemma_on_first_seq_element_elimination(n_state.attestation_duties_queue, n'_state.attestation_duties_queue, i);
            // assert i - 1 >= 0;
            lemma_on_first_seq_element_elimination(n_state.attestation_duties_queue, n'_state.attestation_duties_queue, i-1);
            // assert s_mod.attestation_duties_queue[i-1] == process.attestation_duties_queue[i]; 
            assert inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                dvn,
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
        dvn: DVState, 
        n: BLSPubkey,
        n_state: DVCNodeState,
        n'_state: DVCNodeState,
        index_next_attestation_duty_to_be_served: nat
    )
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n , n_state, index_next_attestation_duty_to_be_served)
    requires |n_state.attestation_duties_queue| > 0
    requires  n'_state.attestation_duties_queue == n_state.attestation_duties_queue[1..]
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n , n_state, index_next_attestation_duty_to_be_served)
    {
        if |n'_state.attestation_duties_queue| > 0
        {
            forall i: nat  |
                inv_attestation_duty_queue_is_ordered_4_body_body_premise(
                    dvn,
                    n, 
                    n'_state,
                    i,
                    index_next_attestation_duty_to_be_served
                )
            ensures 
                var last := n_state.attestation_duties_queue[|n_state.attestation_duties_queue|-1];
                    last.slot == dvn.sequence_attestation_duties_to_be_served[i].attestation_duty.slot 
            {
                assert inv_attestation_duty_queue_is_ordered_4_body_body_premise(
                    dvn,
                    n, 
                    n_state,
                    i,
                    index_next_attestation_duty_to_be_served                     
                );
            }    
        }
    }


    lemma  lemma_on_first_seq_element_elimination<T>(
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


    lemma lemma_pred_4_1_b_new_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state   
    requires index_next_attestation_duty_to_be_served > 0    
    requires inv_g_b_body_body_new(dvn, n, process)
    requires inv_g_a_ii_a_body_body(dvn, n, process)
    requires inv_g_a_iii_body_body(dvn, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_g_d_a_body_body(dvn, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process) 
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, process, index_next_attestation_duty_to_be_served-1)  
    requires is_sequence_attestation_duties_to_be_served_orderd(dvn);
    requires 
                var an' := dvn.sequence_attestation_duties_to_be_served[index_next_attestation_duty_to_be_served-1];
                && an'.attestation_duty == attestation_duty
                && an'.node == n
    ensures inv_g_b_body_body_new(dvn, n, s');
    {
        var new_p := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
        );

        if |process.attestation_duties_queue| == 0 
        {
            assert inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, new_p);  
        }
        else 
        {
            forall i: nat, k, l, t  |
                inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                    dvn,
                    n, 
                    new_p,
                    i,
                    k, 
                    l, 
                    t
                )
            ensures 
                new_p.attestation_duties_queue[i-1].slot == dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot      
            {
                // assert process.attestation_duties_queue != [];
                assert i > 0;


                if i != |new_p.attestation_duties_queue| - 1
                {
                    assert inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                        dvn,
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

                    assert new_p.attestation_duties_queue[i-1].slot <= dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;

                    assert inv_attestation_duty_queue_is_ordered_4_body_body_premise(dvn, n, process, t, index_next_attestation_duty_to_be_served-1);

                    assert new_p.attestation_duties_queue[i-1].slot == dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;
                }

            }   
        }



        lemma_pred_4_1_b_new_f_check_for_next_queued_duty(new_p, s', dvn, n, index_next_attestation_duty_to_be_served);
    }

    lemma lemma_pred_4_1_b_new_f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(process, id, decided_attestation_data).state
    requires inv_g_b_body_body_new(dvn, n, process)
    requires inv_g_a_ii_a_body_body(dvn, n, process)
    requires inv_g_a_iv_a_body_body(dvn, n, process)
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dvn, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process)   
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)

    requires dvn.consensus_on_attestation_data[id].decided_value.isPresent()
    requires dvn.consensus_on_attestation_data[id].decided_value.safe_get() ==  decided_attestation_data 
    ensures inv_g_b_body_body_new(dvn, n, s'); 
    {
        // TODO: Remove below by changing spec
        assume id == process.current_attestation_duty.safe_get().slot;        
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

        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process, s_mod);

        assert inv_g_b_body_body_new(dvn, n, s_mod);

        assert get_upperlimit_decided_instances(s_mod) == process.latest_attestation_duty.safe_get().slot + 1;

        if
            &&  |s_mod.attestation_duties_queue| > 0 
            &&   !s_mod.current_attestation_duty.isPresent()        
        {
            forall an |
                && an in dvn.sequence_attestation_duties_to_be_served.Values 
                && an.node == n 
                && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot   
            ensures      
                    var slot := an.attestation_duty.slot;
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                        ;                        
            {
                var slot := an.attestation_duty.slot;

                if slot > s_mod.latest_attestation_duty.safe_get().slot
                {
                    assert 
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                        ;                    
                }
                else if slot == s_mod.latest_attestation_duty.safe_get().slot
                {
                    assert 
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                        ;                         
                }
                else 
                {
                    assert slot < s_mod.latest_attestation_duty.safe_get().slot;
                    assert 
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                        ;                           
                }

            }
        }
        assert inv_g_a_ii_a_body_body(dvn, n, s_mod);


        lemma_pred_4_1_b_new_f_check_for_next_queued_duty(s_mod, s', dvn, n, index_next_attestation_duty_to_be_served);             
    }  

    lemma lemma_f_listen_for_new_imported_blocks_helper_1(
        dvn: DVState,
        process: DVCNodeState,
        block: BeaconBlock,
        new_consensus_instances_already_decided: map<Slot, AttestationData>
    )
    requires f_listen_for_new_imported_blocks_helper_1.requires(process, block)
    requires new_consensus_instances_already_decided == f_listen_for_new_imported_blocks_helper_1(process, block)
    requires pred_4_1_b(dvn)
    requires pred_4_1_c(dvn)
    ensures 
        forall slot | 
                slot in new_consensus_instances_already_decided
                :: 
                && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                && dvn.consensus_on_attestation_data[slot].decided_value.safe_get() == new_consensus_instances_already_decided[slot]
                ;  
    {
        forall slot | slot in new_consensus_instances_already_decided
        ensures 
            && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
            && dvn.consensus_on_attestation_data[slot].decided_value.safe_get() == new_consensus_instances_already_decided[slot]
            ;         
        {

            var valIndex := bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);


            var a :| 
                && a in block.body.attestations
                && isMyAttestation(a, process, block, valIndex)
                && a.data == new_consensus_instances_already_decided[slot]
            ;

            var an :| assume
                && an in dvn.honest_nodes_states.Keys 
                && a in dvn.honest_nodes_states[an].bn.attestations_submitted
                
                ;

            var hn', att_share: AttestationShare :| pred_4_1_b_exists(dvn, hn', att_share, a);

            assert
            && dvn.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent()
            && dvn.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;

            // assert slot in process.future_att_consensus_instances_already_decided;
            assert
            && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
            && dvn.consensus_on_attestation_data[slot].decided_value.safe_get() == new_consensus_instances_already_decided[slot]
            ;              
        }
    }


    lemma lemma_pred_4_1_b_new_f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires inv_g_b_body_body_new(dvn, n, process)
    requires inv_g_a_ii_a_body_body(dvn, n, process)
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dvn, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process) 
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)
    requires pred_4_1_b(dvn)
    requires pred_4_1_c(dvn)
    requires inv_g_a_iv_a_body_body(dvn, n, process)
    ensures inv_g_b_body_body_new(dvn, n, s');
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

            lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process, s_mod);


            lemma_f_listen_for_new_imported_blocks_helper_1(
                dvn,
                process,
                block,
                new_consensus_instances_already_decided
            );

            assert 
                && dvn.consensus_on_attestation_data[new_process.current_attestation_duty.safe_get().slot].decided_value.isPresent()
                && dvn.consensus_on_attestation_data[new_process.current_attestation_duty.safe_get().slot].decided_value.safe_get() == decided_attestation_data
            ;                        

            assert inv_g_d_a_body_body(dvn, n, s_mod);                  

            assert inv_g_b_body_body_new(dvn, n, s_mod);


            if
                &&  |s_mod.attestation_duties_queue| > 0 
                &&   !s_mod.current_attestation_duty.isPresent()        
            {
                forall an |
                    && an in dvn.sequence_attestation_duties_to_be_served.Values 
                    && an.node == n 
                    && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot   
                ensures      
                        var slot := an.attestation_duty.slot;
                            && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                        
                {
                    var slot := an.attestation_duty.slot;

                    if slot > s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                    
                    }
                    else if slot == s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                         
                    }
                    else 
                    {
                        assert slot < s_mod.latest_attestation_duty.safe_get().slot;
                        assert 
                            && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                           
                    }

                }
            }
            assert inv_g_a_ii_a_body_body(dvn, n, s_mod);                 

            
            lemma_pred_4_1_b_new_f_check_for_next_queued_duty(s_mod, s', dvn, n, index_next_attestation_duty_to_be_served);                    
        }        
    }      
    
    
    // lemma lemma_pred_4_1_b_new_f_check_for_next_queued_duty_fake(
    //     process: DVCNodeState,
    //     s': DVCNodeState,
    //     dvn: DVState,
    //     n: BLSPubkey,
    //     index_next_attestation_duty_to_be_served: nat
    // )
    // requires f_check_for_next_queued_duty.requires(process)
    // requires s' == f_check_for_next_queued_duty(process).state   
    // requires inv_g_b_body_body_new(dvn, n, process)
    // requires inv_g_a_ii_a_body_body(dvn, n, process)
    // requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    // // requires inv_g_d_a_body_body(dvn, n, process)
    // requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process)  

    // ensures inv_g_b_body_body_new(dvn, n, s');
    // decreases process.attestation_duties_queue    
    
    lemma lemma_pred_4_1_b_new_f_check_for_next_queued_duty(
        process: DVCNodeState,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state   
    requires inv_g_b_body_body_new(dvn, n, process)
    requires inv_g_a_ii_a_body_body(dvn, n, process)
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dvn, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process)  

    ensures inv_g_b_body_body_new(dvn, n, s');
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

                if  && |s_mod.attestation_duties_queue| > 0 
                    &&   !s_mod.current_attestation_duty.isPresent()
                {
                  
                    forall an |
                        && an in dvn.sequence_attestation_duties_to_be_served.Values 
                        && an.node == n 
                        && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot
                    ensures 
                        var slot := an.attestation_duty.slot;
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                    ;                          
                    {
                        var slot := an.attestation_duty.slot;
                   
                        if an.attestation_duty.slot < process.attestation_duties_queue[0].slot  
                        {
                            assert 
                                && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                                && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                            ;
                        }
                        else 
                        {
                            var t :|  dvn.sequence_attestation_duties_to_be_served[t] == an;
                            assert process.attestation_duties_queue[0] in process.attestation_duties_queue;
                            var k :|  
                                    && dvn.sequence_attestation_duties_to_be_served[k].node == n 
                                    && dvn.sequence_attestation_duties_to_be_served[k].attestation_duty == process.attestation_duties_queue[0];
                            assert process.attestation_duties_queue[1] in process.attestation_duties_queue;
                            var l :|  
                                    && dvn.sequence_attestation_duties_to_be_served[l].node == n 
                                    && dvn.sequence_attestation_duties_to_be_served[l].attestation_duty == process.attestation_duties_queue[1];   

                            lemma_inv_attestation_duty_queue_is_ordered_3_body_body(
                                dvn,
                                n,
                                process,
                                1,
                                k,
                                l,
                                t
                            ); 

                        
                            assert 
                                && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                                && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                            ;
                            
                        }
                    }                  
                }
                assert inv_g_a_ii_a_body_body(dvn, n, s_mod);

                forall i: nat, k, l, t  |
                    inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                        dvn,
                        n, 
                        s_mod,
                        i,
                        k, 
                        l, 
                        t
                    )
                ensures 
                    s_mod.attestation_duties_queue[i-1].slot == dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot      
                {
                    assert process.attestation_duties_queue != [];
                    assert i > 0;
                    lemma_on_first_seq_element_elimination(process.attestation_duties_queue, s_mod.attestation_duties_queue, i);
                    // assert i - 1 >= 0;
                    lemma_on_first_seq_element_elimination(process.attestation_duties_queue, s_mod.attestation_duties_queue, i-1);
                    // assert s_mod.attestation_duties_queue[i-1] == process.attestation_duties_queue[i]; 
                    assert inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                        dvn,
                        n, 
                        process,
                        i+1,
                        k, 
                        l, 
                        t                        
                    );
                }   

                forall ad  |
                    && ad in s_mod.attestation_duties_queue
                ensures ad in process.attestation_duties_queue
                {
                    var i :| 0 <= i < |s_mod.attestation_duties_queue|
                                && s_mod.attestation_duties_queue[i] == ad;
                    assert ad in process.attestation_duties_queue;
                }
                    // ::
                    // exists i: nat :: 
                    //     && i < index_next_attestation_duty_to_be_served
                    //     && var an := dvn.sequence_attestation_duties_to_be_served[i];
                    //     && an.attestation_duty == ad
                    //     && an.node == n                       

                lemma_pred_4_1_b_new_f_check_for_next_queued_duty(s_mod, s', dvn, n , index_next_attestation_duty_to_be_served);
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
                    assert inv_g_b_body_body_new(dvn, n, s');
                }
                else 
                {
                    assert inv_g_b_body_body_new(dvn, n, s');
                }

                
            }
        } 
        else 
        {
            assert inv_g_b_body_body_new(dvn, n, s');
        }       
    }    

    lemma lemma_pred_4_1_b_new_helper_transpose_to_new_s_1(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCNodeState,
        n: BLSPubkey
    )
    requires NextEvent(s, event, s')    
    requires inv_g_a_ii_a_body_body(s, n, s_node)
    requires invNetwork(s)
    requires inv1(s)
    requires inv3(s)
    requires inv53(s)  
    ensures inv_g_a_ii_a_body_body(s', n, s_node)        
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
                lemma_pred_4_1_g_iii_helper2(s, event, s', slot);

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

    lemma lemma_pred_4_1_b_new_helper_transpose_to_new_s_2(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCNodeState,
        n: BLSPubkey
    )
    requires NextEvent(s, event, s')    
    requires inv_g_a_iii_body_body(s, n, s_node, s.index_next_attestation_duty_to_be_served)
    requires invNetwork(s)
    requires inv1(s)
    requires inv3(s)
    requires inv53(s)  
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
                lemma_pred_4_1_g_iii_helper2(s, event, s', slot);

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

    lemma lemma_pred_4_1_b_new_helper_transpose_to_new_s_3(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCNodeState,
        n: BLSPubkey
    )
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

    lemma lemma_pred_4_1_b_new_helper_transpose_to_new_s_4(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCNodeState,
        n: BLSPubkey
    )
    requires NextEvent(s, event, s')    
    requires inv_g_a_iv_a_body_body(s, n, s_node)
    requires invNetwork(s)
    requires inv1(s)
    requires inv3(s)
    requires inv53(s)  
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
                lemma_pred_4_1_g_iii_helper2(s, event, s', slot);

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

    lemma lemma_pred_4_1_b_new_helper_transpose_to_new_s_multiple(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCNodeState,
        n: BLSPubkey
    )
    requires NextEvent(s, event, s')    
    requires inv_g_iii_b_body_body(s, n, s_node, s.index_next_attestation_duty_to_be_served)
    // requires inv_attestation_duty_queue_is_ordered_3_body_body(s, n, s_node)
    // requires inv_attestation_duty_queue_is_ordered_4_body_body(s, n, s_node, s.index_next_attestation_duty_to_be_served)

    ensures inv_g_iii_b_body_body(s', n, s_node, s.index_next_attestation_duty_to_be_served)
    // ensures inv_attestation_duty_queue_is_ordered_3_body_body(s', n, s_node)
    // ensures inv_attestation_duty_queue_is_ordered_4_body_body(s', n, s_node, s.index_next_attestation_duty_to_be_served)
    {
        assert s'.index_next_attestation_duty_to_be_served <= s'.index_next_attestation_duty_to_be_served <= s'.index_next_attestation_duty_to_be_served + 1;
        
    }   

    lemma lemma_pred_4_1_b_new_helper_easy(
        s: DVState,
        event: DV.Event,
        s_node: DVCNodeState,
        s'_node: DVCNodeState,
        n: BLSPubkey
    )
    requires inv_g_b_body_body_new(s, n, s_node)
    requires s_node.latest_attestation_duty == s'_node.latest_attestation_duty
    requires s_node.current_attestation_duty == s'_node.current_attestation_duty
    requires s_node.attestation_slashing_db <= s'_node.attestation_slashing_db
    ensures inv_g_b_body_body_new(s, n, s'_node)        
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

    predicate lemma_pred_4_1_b_new_precond(s: DVState) 
    {
        && inv1(s)
        && inv2(s)
        && inv3(s)
        && inv53(s)    
        && invNetwork(s)
        && pred_4_1_g_b_new(s) //
        && inv_g_a_ii_a(s) //
        && pred_4_1_g_iii_b(s) //
        && inv_g_d_a(s) //
        && inv_attestation_duty_queue_is_ordered_3(s) //  
        && inv_attestation_duty_queue_is_ordered_4(s) //    
        && inv_g_a_iii(s) //
        && inv_g_a_iv(s) //
        && pred_4_1_b(s) //
        && pred_4_1_c(s) //  
        && is_sequence_attestation_duties_to_be_served_orderd(s) //
        && pred_inv_current_latest_attestation_duty_match(s)


        && pred_4_1_g_iii(s) 

        && construct_signed_attestation_signature_assumptions_helper(
            s.construct_signed_attestation_signature,
            s.dv_pubkey,
            s.all_nodes
        )    
        && pred_rcvd_attestation_shares_is_in_all_messages_sent(s) 
        && pred_4_1_f_b(s)
        && inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)      
        && pred_4_1_f_a(s)    
        && pred_4_1_g_i(s)    
        && pred_4_1_g_i_for_dvc(s)         
    }

    lemma lemma_pred_4_1_b_new_helper_summary(
        s: DVState,
        event: DV.Event,
        s': DVState        
    )
    requires NextEvent(s, event, s')
    requires event.HonestNodeTakingStep?
    requires lemma_pred_4_1_b_new_precond(s)
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lemma_pred_4_1_g_iii_helper3a(s, event, s', s_node, node);
                lemma_pred_4_1_g_iii_helper3c(s, event, s', s_node, node);
                lemma_pred_4_1_b_new_helper_transpose_to_new_s_1(s, event, s', s_node, node);
                lemma_pred_4_1_b_new_helper_transpose_to_new_s_2(s, event, s', s_node, node);
                lemma_pred_4_1_b_new_helper_transpose_to_new_s_3(s, event, s', s_node, node);
                lemma_pred_4_1_b_new_helper_transpose_to_new_s_4(s, event, s', s_node, node);

                lemma_pred_4_1_b_new_helper_transpose_to_new_s_multiple(s, event, s', s_node, node);

                // lemma_pred_4_1_b(s, event, s');
                // lemma_pred_4_1_c(s, event, s');

                lemma_inv_sequence_attestation_duties_to_be_served_orderd(s, event, s');

                // assert inv_g_b_body_body_new(s', node, s_node);
                // assert inv_g_d_a_body_body(s', node, s_node);
                // assert inv_g_a_ii_a_body_body(s', node, s_node);
                // assert inv_g_iii_b_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                // assert inv_g_a_iii_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                // assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node);
                // assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                // assert pred_4_1_b(s');
                // assert pred_4_1_c(s');             
                // assert inv_g_a_iv_a_body_body(s', node, s_node);
        }        
    }   

    lemma lemma_ServeAttstationDuty(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEvent(s, event, s')    
    requires event.HonestNodeTakingStep?
    requires event.event.ServeAttstationDuty?
    ensures
                        var attestation_duty := event.event.attestation_duty;
                        var an := s'.sequence_attestation_duties_to_be_served[s'.index_next_attestation_duty_to_be_served - 1];

                        && attestation_duty == an.attestation_duty
                        && event.node == an.node    
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];


                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        assert s.sequence_attestation_duties_to_be_served == s'.sequence_attestation_duties_to_be_served;
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;

                        var an := s'.sequence_attestation_duties_to_be_served[s'.index_next_attestation_duty_to_be_served - 1];

                        assert attestation_duty == an.attestation_duty;
                        assert node == an.node;

                }
        }        
    }

    lemma lemma_NonServeAttstationDuty(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEvent(s, event, s')    
    requires event.HonestNodeTakingStep?
    requires !event.event.ServeAttstationDuty?
    ensures s'.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;
    ensures s'.sequence_attestation_duties_to_be_served == s'.sequence_attestation_duties_to_be_served  
    {
     
    }    
    
    lemma lemma_pred_4_1_b_new(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEvent(s, event, s')
    requires lemma_pred_4_1_b_new_precond(s)
    ensures pred_4_1_g_b_new(s');  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lemma_pred_4_1_g_iii_helper3a(s, event, s', s_node, node);
                lemma_pred_4_1_g_iii_helper3c(s, event, s', s_node, node);
                lemma_pred_4_1_b_new_helper_transpose_to_new_s_1(s, event, s', s_node, node);
                lemma_pred_4_1_b_new_helper_transpose_to_new_s_2(s, event, s', s_node, node);
                lemma_pred_4_1_b_new_helper_transpose_to_new_s_3(s, event, s', s_node, node);
                lemma_pred_4_1_b_new_helper_transpose_to_new_s_4(s, event, s', s_node, node);

                lemma_pred_4_1_b_new_helper_transpose_to_new_s_multiple(s, event, s', s_node, node);

                lemma_pred_4_1_b(s, event, s');
                lemma_pred_4_1_c(s, event, s');

                lemma_inv_sequence_attestation_duties_to_be_served_orderd(s, event, s');

                assert inv_g_b_body_body_new(s', node, s_node);
                assert inv_g_d_a_body_body(s', node, s_node);
                assert inv_g_a_ii_a_body_body(s', node, s_node);
                assert inv_g_iii_b_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_g_a_iii_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node);
                assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert pred_4_1_b(s');
                assert pred_4_1_c(s');             
                assert inv_g_a_iv_a_body_body(s', node, s_node);
                assert is_sequence_attestation_duties_to_be_served_orderd(s');

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lemma_ServeAttstationDuty(s, event, s');
                        lemma_pred_4_1_b_new_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_g_b_body_body_new(s', node, s'_node);                     
 
                              

                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lemma_pred_4_1_g_iii_helper5(s, event, s');                 
                        lemma_pred_4_1_b_new_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_g_b_body_body_new(s', node, s'_node);                        
               
                   
                    case ReceviedAttesttionShare(attestation_share) => 
                        lemma_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        lemma_pred_4_1_b_new_helper_easy(s', event, s_node, s'_node, node );
                        

                    case ImportedNewBlock(block) => 
                        var s_node2 := add_block_to_bn(s_node, nodeEvent.block);
                        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node, s_node2);
                        lemma_pred_4_1_b_new_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_g_b_body_body_new(s', node, s'_node);                     
                    
                 
                    case ResendAttestationShares => 
                        lemma_pred_4_1_b_new_helper_easy(s', event, s_node, s'_node, node );

                   
                    case NoEvent => 
                        lemma_pred_4_1_b_new_helper_easy(s', event, s_node, s'_node, node );
                }
                assert inv_g_b_body_body_new(s', node, s'_node);  
                

                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_g_b_body_body_new(s', hn, s'.honest_nodes_states[hn]); 
                {
                    if hn != node 
                    {
                        // lemma_pred_4_1_g_iii_helper3(s, event, s', s.honest_nodes_states[hn]);
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lemma_pred_4_1_g_iii_helper3a(s, event, s', s.honest_nodes_states[hn], hn);
                        lemma_pred_4_1_b_new_helper_easy(s', event, s.honest_nodes_states[hn], s'.honest_nodes_states[hn], hn);
                        // assert inv_g_b_body_body_new(s', hn, s'.honest_nodes_states[hn]);                        
                    }
                }     
                assert pred_4_1_g_b_new(s');                  
        

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                 forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_g_b_body_body_new(s', hn, s'.honest_nodes_states[hn]); 
                {

                    {
                        // lemma_pred_4_1_g_iii_helper3(s, event, s', s.honest_nodes_states[hn]);
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lemma_pred_4_1_g_iii_helper3a(s, event, s', s.honest_nodes_states[hn], hn);
                        lemma_pred_4_1_b_new_helper_easy(s', event, s.honest_nodes_states[hn], s'.honest_nodes_states[hn], hn);
                        // assert inv_g_b_body_body_new(s', hn, s'.honest_nodes_states[hn]);                        
                    }
                }     
                assert pred_4_1_g_b_new(s'); 

        }
    }  

    lemma lemma_inv_g_a_ii_a_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state   
    requires index_next_attestation_duty_to_be_served > 0    
    requires inv_g_a_ii_a_body_body(dvn, n, process)
    requires inv_g_a_iii_body_body(dvn, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_g_d_a_body_body(dvn, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process) 
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, process, index_next_attestation_duty_to_be_served-1)  
    requires is_sequence_attestation_duties_to_be_served_orderd(dvn);
    requires 
                var an' := dvn.sequence_attestation_duties_to_be_served[index_next_attestation_duty_to_be_served-1];
                && an'.attestation_duty == attestation_duty
                && an'.node == n
    ensures inv_g_a_ii_a_body_body(dvn, n, s');
    {
        var new_p := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
        );

        if |process.attestation_duties_queue| == 0 
        {
            assert inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, new_p);  
        }
        else 
        {
            forall i: nat, k, l, t  |
                inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                    dvn,
                    n, 
                    new_p,
                    i,
                    k, 
                    l, 
                    t
                )
            ensures 
                new_p.attestation_duties_queue[i-1].slot == dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot      
            {
                // assert process.attestation_duties_queue != [];
                assert i > 0;


                if i != |new_p.attestation_duties_queue| - 1
                {
                    assert inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                        dvn,
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

                    assert new_p.attestation_duties_queue[i-1].slot <= dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;

                    assert inv_attestation_duty_queue_is_ordered_4_body_body_premise(dvn, n, process, t, index_next_attestation_duty_to_be_served-1);

                    assert new_p.attestation_duties_queue[i-1].slot == dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;
                }

            }   
        }



        lemma_inv_g_a_ii_a_f_check_for_next_queued_duty(new_p, s', dvn, n, index_next_attestation_duty_to_be_served);
    }

    lemma lemma_inv_g_a_ii_a_f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(process, id, decided_attestation_data).state
    requires inv_g_b_body_body_new(dvn, n, process)
    requires inv_g_a_ii_a_body_body(dvn, n, process)
    requires inv_g_a_iv_a_body_body(dvn, n, process)
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dvn, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process)   
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)

    requires dvn.consensus_on_attestation_data[id].decided_value.isPresent()
    requires dvn.consensus_on_attestation_data[id].decided_value.safe_get() ==  decided_attestation_data 
    ensures inv_g_a_ii_a_body_body(dvn, n, s'); 
    {
        // TODO: Remove below by changing spec
        assume id == process.current_attestation_duty.safe_get().slot;        
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

        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process, s_mod);

        assert get_upperlimit_decided_instances(s_mod) == process.latest_attestation_duty.safe_get().slot + 1;

        if
            &&  |s_mod.attestation_duties_queue| > 0 
            &&   !s_mod.current_attestation_duty.isPresent()        
        {
            forall an |
                && an in dvn.sequence_attestation_duties_to_be_served.Values 
                && an.node == n 
                && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot   
            ensures      
                    var slot := an.attestation_duty.slot;
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                        ;                        
            {
                var slot := an.attestation_duty.slot;

                if slot > s_mod.latest_attestation_duty.safe_get().slot
                {
                    assert 
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                        ;                    
                }
                else if slot == s_mod.latest_attestation_duty.safe_get().slot
                {
                    assert 
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                        ;                         
                }
                else 
                {
                    assert slot < s_mod.latest_attestation_duty.safe_get().slot;
                    assert 
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                        ;                           
                }

            }
        }
        assert inv_g_a_ii_a_body_body(dvn, n, s_mod);


        lemma_inv_g_a_ii_a_f_check_for_next_queued_duty(s_mod, s', dvn, n, index_next_attestation_duty_to_be_served);             
    }  

    lemma lemma_inv_g_a_ii_a_f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires inv_g_b_body_body_new(dvn, n, process)
    requires inv_g_a_ii_a_body_body(dvn, n, process)
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dvn, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process) 
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)
    requires pred_4_1_b(dvn)
    requires pred_4_1_c(dvn)
    requires inv_g_a_iv_a_body_body(dvn, n, process)
    ensures inv_g_a_ii_a_body_body(dvn, n, s');
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

            lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process, s_mod);


            lemma_f_listen_for_new_imported_blocks_helper_1(
                dvn,
                process,
                block,
                new_consensus_instances_already_decided
            );

            assert 
                && dvn.consensus_on_attestation_data[new_process.current_attestation_duty.safe_get().slot].decided_value.isPresent()
                && dvn.consensus_on_attestation_data[new_process.current_attestation_duty.safe_get().slot].decided_value.safe_get() == decided_attestation_data
            ;                        

            assert inv_g_d_a_body_body(dvn, n, s_mod);                  

            assert inv_g_b_body_body_new(dvn, n, s_mod);


            if
                &&  |s_mod.attestation_duties_queue| > 0 
                &&   !s_mod.current_attestation_duty.isPresent()        
            {
                forall an |
                    && an in dvn.sequence_attestation_duties_to_be_served.Values 
                    && an.node == n 
                    && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot   
                ensures      
                        var slot := an.attestation_duty.slot;
                            && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                        
                {
                    var slot := an.attestation_duty.slot;

                    if slot > s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                    
                    }
                    else if slot == s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                         
                    }
                    else 
                    {
                        assert slot < s_mod.latest_attestation_duty.safe_get().slot;
                        assert 
                            && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                           
                    }

                }
            }
            assert inv_g_a_ii_a_body_body(dvn, n, s_mod);                 

            forall an |
                && an in dvn.sequence_attestation_duties_to_be_served.Values 
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

            
            lemma_inv_g_a_ii_a_f_check_for_next_queued_duty(s_mod, s', dvn, n, index_next_attestation_duty_to_be_served);                    
        }        
    }          

    lemma lemma_inv_g_a_ii_a_f_check_for_next_queued_duty(
        process: DVCNodeState,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state  
    requires inv_g_a_ii_a_body_body(dvn, n, process)
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dvn, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process)  
    ensures inv_g_a_ii_a_body_body(dvn, n, s')
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

                // TODO: Put the following proofs in a lemma. They are repeates elsewhere like in
                // lemma_pred_4_1_b_new_f_check_for_next_queued_duty
                if  && |s_mod.attestation_duties_queue| > 0 
                    &&   !s_mod.current_attestation_duty.isPresent()
                {
                  
                    forall an |
                        && an in dvn.sequence_attestation_duties_to_be_served.Values 
                        && an.node == n 
                        && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot
                    ensures 
                        var slot := an.attestation_duty.slot;
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                    ;                          
                    {
                        var slot := an.attestation_duty.slot;
                   
                        if an.attestation_duty.slot < process.attestation_duties_queue[0].slot  
                        {
                            assert 
                                && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                                && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                            ;
                        }
                        else 
                        {
                            var t :|  dvn.sequence_attestation_duties_to_be_served[t] == an;
                            assert process.attestation_duties_queue[0] in process.attestation_duties_queue;
                            var i :|  
                                    && dvn.sequence_attestation_duties_to_be_served[i].node == n 
                                    && dvn.sequence_attestation_duties_to_be_served[i].attestation_duty == process.attestation_duties_queue[0];
                            assert process.attestation_duties_queue[1] in process.attestation_duties_queue;
                            var j :|  
                                    && dvn.sequence_attestation_duties_to_be_served[j].node == n 
                                    && dvn.sequence_attestation_duties_to_be_served[j].attestation_duty == process.attestation_duties_queue[1];   

                            lemma_inv_attestation_duty_queue_is_ordered_3_body_body(
                                dvn,
                                n,
                                process,
                                1,
                                i,
                                j,
                                t
                            ); 

                        
                            assert 
                                && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                                && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                            ;
                            
                        }
                    }                  
                }
                assert inv_g_a_ii_a_body_body(dvn, n, s_mod);


                forall i: nat, k, l, t  |
                    inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                        dvn,
                        n, 
                        s_mod,
                        i,
                        k, 
                        l, 
                        t
                    )
                ensures 
                    s_mod.attestation_duties_queue[i-1].slot == dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot      
                {
                    assert process.attestation_duties_queue != [];
                    assert i > 0;
                    lemma_on_first_seq_element_elimination(process.attestation_duties_queue, s_mod.attestation_duties_queue, i);
                    // assert i - 1 >= 0;
                    lemma_on_first_seq_element_elimination(process.attestation_duties_queue, s_mod.attestation_duties_queue, i-1);
                    // assert s_mod.attestation_duties_queue[i-1] == process.attestation_duties_queue[i]; 
                    assert inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                        dvn,
                        n, 
                        process,
                        i+1,
                        k, 
                        l, 
                        t                        
                    );
                }   

                forall ad  |
                    && ad in s_mod.attestation_duties_queue
                ensures ad in process.attestation_duties_queue
                {
                    var i :| 0 <= i < |s_mod.attestation_duties_queue|
                                && s_mod.attestation_duties_queue[i] == ad;
                    assert ad in process.attestation_duties_queue;
                }                              



                lemma_inv_g_a_ii_a_f_check_for_next_queued_duty(s_mod, s', dvn, n , index_next_attestation_duty_to_be_served);
            }
            else 
            {
                var new_process := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..]
                );   

                var queue_head := process.attestation_duties_queue[0];       


                assert inv_g_a_ii_a_body_body(dvn, n, s');

            }
        } 
        else 
        {
            // assert inv_g_b_body_body_new(dvn, n, s');
        }       
    }       

    lemma lemma_inv_g_a_ii_a_helper_easy(
        s: DVState,
        event: DV.Event,
        s_node: DVCNodeState,
        s'_node: DVCNodeState,
        n: BLSPubkey
    )
    requires inv_g_a_ii_a_body_body(s, n, s_node)
    requires s_node.attestation_duties_queue == s'_node.attestation_duties_queue
    requires s_node.current_attestation_duty == s'_node.current_attestation_duty
    requires s_node.attestation_slashing_db <= s'_node.attestation_slashing_db
    ensures inv_g_a_ii_a_body_body(s, n, s'_node)        
    {        
    }       

    lemma lemma_inv_g_a_ii_a(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEvent(s, event, s')
    requires lemma_pred_4_1_b_new_precond(s)
    ensures inv_g_a_ii_a(s');  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lemma_pred_4_1_g_iii_helper3a(s, event, s', s_node, node);
                lemma_pred_4_1_g_iii_helper3c(s, event, s', s_node, node);
                lemma_pred_4_1_b_new_helper_transpose_to_new_s_1(s, event, s', s_node, node);
                lemma_pred_4_1_b_new_helper_transpose_to_new_s_2(s, event, s', s_node, node);
                lemma_pred_4_1_b_new_helper_transpose_to_new_s_3(s, event, s', s_node, node);
                lemma_pred_4_1_b_new_helper_transpose_to_new_s_4(s, event, s', s_node, node);

                lemma_pred_4_1_b_new_helper_transpose_to_new_s_multiple(s, event, s', s_node, node);

                lemma_pred_4_1_b(s, event, s');
                lemma_pred_4_1_c(s, event, s');

                lemma_inv_sequence_attestation_duties_to_be_served_orderd(s, event, s');

                assert inv_g_b_body_body_new(s', node, s_node);
                assert inv_g_d_a_body_body(s', node, s_node);
                assert inv_g_a_ii_a_body_body(s', node, s_node);
                assert inv_g_iii_b_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_g_a_iii_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node);
                assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert pred_4_1_b(s');
                assert pred_4_1_c(s');             
                assert inv_g_a_iv_a_body_body(s', node, s_node);
                assert is_sequence_attestation_duties_to_be_served_orderd(s');

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lemma_ServeAttstationDuty(s, event, s');
                        lemma_inv_g_a_ii_a_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_g_a_ii_a_body_body(s', node, s'_node);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lemma_pred_4_1_g_iii_helper5(s, event, s');                 
                        lemma_inv_g_a_ii_a_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_g_a_ii_a_body_body(s', node, s'_node);                        
               
                   
                    case ReceviedAttesttionShare(attestation_share) => 
                        lemma_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        lemma_inv_g_a_ii_a_helper_easy(s', event, s_node, s'_node, node );
                        

                    case ImportedNewBlock(block) => 
                        var s_node2 := add_block_to_bn(s_node, nodeEvent.block);
                        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node, s_node2);
                        lemma_inv_g_a_ii_a_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_g_a_ii_a_body_body(s', node, s'_node);                     
                    
                 
                    case ResendAttestationShares => 
                        lemma_f_resend_attestation_share_constants(s_node, s'_node);
                        lemma_inv_g_a_ii_a_helper_easy(s', event, s_node, s'_node, node );

                   
                    case NoEvent => 
                        lemma_inv_g_a_ii_a_helper_easy(s', event, s_node, s'_node, node );
                }
                assert inv_g_a_ii_a_body_body(s', node, s'_node);  
                

                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_g_a_ii_a_body_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lemma_pred_4_1_b_new_helper_transpose_to_new_s_1(s, event, s', s.honest_nodes_states[hn], hn);
                        lemma_inv_g_a_ii_a_helper_easy(s', event, s.honest_nodes_states[hn], s'.honest_nodes_states[hn], hn);
                    }
                }     
                assert inv_g_a_ii_a(s');                  
        

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_g_a_ii_a_body_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    // if hn != node 
                    // {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lemma_pred_4_1_b_new_helper_transpose_to_new_s_1(s, event, s', s.honest_nodes_states[hn], hn);
                        lemma_inv_g_a_ii_a_helper_easy(s', event, s.honest_nodes_states[hn], s'.honest_nodes_states[hn], hn);
                    // }
                }     
                assert inv_g_a_ii_a(s'); 

        }
    }    

    lemma lemma_inv_g_iii_b_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state   
    requires index_next_attestation_duty_to_be_served > 0    
    requires inv_g_a_ii_a_body_body(dvn, n, process)
    requires inv_g_a_iii_body_body(dvn, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_g_d_a_body_body(dvn, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process) 
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, process, index_next_attestation_duty_to_be_served-1)  
    requires is_sequence_attestation_duties_to_be_served_orderd(dvn);
    requires 
                var an' := dvn.sequence_attestation_duties_to_be_served[index_next_attestation_duty_to_be_served-1];
                && an'.attestation_duty == attestation_duty
                && an'.node == n
    ensures inv_g_iii_b_body_body(dvn, n, s', index_next_attestation_duty_to_be_served);
    {
        var new_p := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
        );

        if |process.attestation_duties_queue| == 0 
        {
            assert inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, new_p);  
        }
        else 
        {
            forall i: nat, k, l, t  |
                inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                    dvn,
                    n, 
                    new_p,
                    i,
                    k, 
                    l, 
                    t
                )
            ensures 
                new_p.attestation_duties_queue[i-1].slot == dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot      
            {
                // assert process.attestation_duties_queue != [];
                assert i > 0;


                if i != |new_p.attestation_duties_queue| - 1
                {
                    assert inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                        dvn,
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

                    assert new_p.attestation_duties_queue[i-1].slot <= dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;

                    assert inv_attestation_duty_queue_is_ordered_4_body_body_premise(dvn, n, process, t, index_next_attestation_duty_to_be_served-1);

                    assert new_p.attestation_duties_queue[i-1].slot == dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;
                }

            }   
        }



        lemma_inv_g_iii_b_f_check_for_next_queued_duty(new_p, s', dvn, n, index_next_attestation_duty_to_be_served);
    }

    lemma lemma_inv_g_iii_b_f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(process, id, decided_attestation_data).state
    requires inv_g_b_body_body_new(dvn, n, process)
    requires inv_g_a_ii_a_body_body(dvn, n, process)
    requires inv_g_a_iv_a_body_body(dvn, n, process)
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dvn, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process)   
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)

    requires dvn.consensus_on_attestation_data[id].decided_value.isPresent()
    requires dvn.consensus_on_attestation_data[id].decided_value.safe_get() ==  decided_attestation_data 
    ensures inv_g_iii_b_body_body(dvn, n, s', index_next_attestation_duty_to_be_served); 
    {
        // TODO: Remove below by changing spec
        assume id == process.current_attestation_duty.safe_get().slot;        
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

        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process, s_mod);

        assert get_upperlimit_decided_instances(s_mod) == process.latest_attestation_duty.safe_get().slot + 1;

        if
            &&  |s_mod.attestation_duties_queue| > 0 
            &&   !s_mod.current_attestation_duty.isPresent()        
        {
            forall an |
                && an in dvn.sequence_attestation_duties_to_be_served.Values 
                && an.node == n 
                && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot   
            ensures      
                    var slot := an.attestation_duty.slot;
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                        ;                        
            {
                var slot := an.attestation_duty.slot;

                if slot > s_mod.latest_attestation_duty.safe_get().slot
                {
                    assert 
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                        ;                    
                }
                else if slot == s_mod.latest_attestation_duty.safe_get().slot
                {
                    assert 
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                        ;                         
                }
                else 
                {
                    assert slot < s_mod.latest_attestation_duty.safe_get().slot;
                    assert 
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                        ;                           
                }

            }
        }
        assert inv_g_a_ii_a_body_body(dvn, n, s_mod);


        lemma_inv_g_iii_b_f_check_for_next_queued_duty(s_mod, s', dvn, n, index_next_attestation_duty_to_be_served);             
    } 

    lemma lemma_inv_g_iii_b_f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires inv_g_b_body_body_new(dvn, n, process)
    requires inv_g_a_ii_a_body_body(dvn, n, process)
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dvn, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process) 
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)
    requires pred_4_1_b(dvn)
    requires pred_4_1_c(dvn)
    requires inv_g_a_iv_a_body_body(dvn, n, process)
    ensures inv_g_iii_b_body_body(dvn, n, s', index_next_attestation_duty_to_be_served);
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

            lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process, s_mod);


            lemma_f_listen_for_new_imported_blocks_helper_1(
                dvn,
                process,
                block,
                new_consensus_instances_already_decided
            );

            assert 
                && dvn.consensus_on_attestation_data[new_process.current_attestation_duty.safe_get().slot].decided_value.isPresent()
                && dvn.consensus_on_attestation_data[new_process.current_attestation_duty.safe_get().slot].decided_value.safe_get() == decided_attestation_data
            ;                        

            assert inv_g_d_a_body_body(dvn, n, s_mod);                  

            assert inv_g_b_body_body_new(dvn, n, s_mod);


            if
                &&  |s_mod.attestation_duties_queue| > 0 
                &&   !s_mod.current_attestation_duty.isPresent()        
            {
                forall an |
                    && an in dvn.sequence_attestation_duties_to_be_served.Values 
                    && an.node == n 
                    && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot   
                ensures      
                        var slot := an.attestation_duty.slot;
                            && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                        
                {
                    var slot := an.attestation_duty.slot;

                    if slot > s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                    
                    }
                    else if slot == s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                         
                    }
                    else 
                    {
                        assert slot < s_mod.latest_attestation_duty.safe_get().slot;
                        assert 
                            && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                           
                    }

                }
            }
            assert inv_g_a_ii_a_body_body(dvn, n, s_mod);                 

            forall an |
                && an in dvn.sequence_attestation_duties_to_be_served.Values 
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

            
            lemma_inv_g_iii_b_f_check_for_next_queued_duty(s_mod, s', dvn, n, index_next_attestation_duty_to_be_served);                    
        }        
    }   

    lemma lemma_inv_g_iii_b_f_check_for_next_queued_duty(
        process: DVCNodeState,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state  
    requires inv_g_a_ii_a_body_body(dvn, n, process)
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_d_a_body_body(dvn, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process)  
    ensures inv_g_iii_b_body_body(dvn, n, s', index_next_attestation_duty_to_be_served)
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

                // TODO: Put the following proofs in a lemma. They are repeates elsewhere like in
                // lemma_pred_4_1_b_new_f_check_for_next_queued_duty
                if  && |s_mod.attestation_duties_queue| > 0 
                    &&   !s_mod.current_attestation_duty.isPresent()
                {
                  
                    forall an |
                        && an in dvn.sequence_attestation_duties_to_be_served.Values 
                        && an.node == n 
                        && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot
                    ensures 
                        var slot := an.attestation_duty.slot;
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                    ;                          
                    {
                        var slot := an.attestation_duty.slot;
                   
                        if an.attestation_duty.slot < process.attestation_duties_queue[0].slot  
                        {
                            assert 
                                && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                                && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                            ;
                        }
                        else 
                        {
                            var t :|  dvn.sequence_attestation_duties_to_be_served[t] == an;
                            assert process.attestation_duties_queue[0] in process.attestation_duties_queue;
                            var i :|  
                                    && dvn.sequence_attestation_duties_to_be_served[i].node == n 
                                    && dvn.sequence_attestation_duties_to_be_served[i].attestation_duty == process.attestation_duties_queue[0];
                            assert process.attestation_duties_queue[1] in process.attestation_duties_queue;
                            var j :|  
                                    && dvn.sequence_attestation_duties_to_be_served[j].node == n 
                                    && dvn.sequence_attestation_duties_to_be_served[j].attestation_duty == process.attestation_duties_queue[1];   

                            lemma_inv_attestation_duty_queue_is_ordered_3_body_body(
                                dvn,
                                n,
                                process,
                                1,
                                i,
                                j,
                                t
                            ); 

                        
                            assert 
                                && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                                && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                            ;
                            
                        }
                    }                  
                }
                assert inv_g_a_ii_a_body_body(dvn, n, s_mod);


                forall i: nat, k, l, t  |
                    inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                        dvn,
                        n, 
                        s_mod,
                        i,
                        k, 
                        l, 
                        t
                    )
                ensures 
                    s_mod.attestation_duties_queue[i-1].slot == dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot      
                {
                    assert process.attestation_duties_queue != [];
                    assert i > 0;
                    lemma_on_first_seq_element_elimination(process.attestation_duties_queue, s_mod.attestation_duties_queue, i);
                    // assert i - 1 >= 0;
                    lemma_on_first_seq_element_elimination(process.attestation_duties_queue, s_mod.attestation_duties_queue, i-1);
                    // assert s_mod.attestation_duties_queue[i-1] == process.attestation_duties_queue[i]; 
                    assert inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                        dvn,
                        n, 
                        process,
                        i+1,
                        k, 
                        l, 
                        t                        
                    );
                }   

                forall ad  |
                    && ad in s_mod.attestation_duties_queue
                ensures ad in process.attestation_duties_queue
                {
                    var i :| 0 <= i < |s_mod.attestation_duties_queue|
                                && s_mod.attestation_duties_queue[i] == ad;
                    assert ad in process.attestation_duties_queue;
                }                              



                lemma_inv_g_iii_b_f_check_for_next_queued_duty(s_mod, s', dvn, n , index_next_attestation_duty_to_be_served);
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

                assert inv_g_iii_b_body_body(dvn, n, s', index_next_attestation_duty_to_be_served);

            }
        } 
        else 
        {
            // assert inv_g_b_body_body_new(dvn, n, s');
        }       
    }             

    lemma lemma_inv_g_iii_b_helper_easy(
        s: DVState,
        event: DV.Event,
        s_node: DVCNodeState,
        s'_node: DVCNodeState,
        n: BLSPubkey
    )
    requires inv_g_iii_b_body_body(s, n, s_node, s.index_next_attestation_duty_to_be_served)
    requires s_node.attestation_duties_queue == s'_node.attestation_duties_queue
    ensures inv_g_iii_b_body_body(s, n, s'_node, s.index_next_attestation_duty_to_be_served)        
    {        
    }    

    lemma lemma_4_1_g_iii_b_helper_honest(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEvent(s, event, s')
    requires lemma_pred_4_1_b_new_precond(s)
    requires event.HonestNodeTakingStep?
    ensures inv_g_iii_b_body_body(s', event.node, s'.honest_nodes_states[event.node], s'.index_next_attestation_duty_to_be_served); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lemma_pred_4_1_g_iii_helper3a(s, event, s', s_node, node);
                lemma_pred_4_1_g_iii_helper3c(s, event, s', s_node, node);
                lemma_pred_4_1_b_new_helper_transpose_to_new_s_1(s, event, s', s_node, node);
                lemma_pred_4_1_b_new_helper_transpose_to_new_s_2(s, event, s', s_node, node);
                lemma_pred_4_1_b_new_helper_transpose_to_new_s_3(s, event, s', s_node, node);
                lemma_pred_4_1_b_new_helper_transpose_to_new_s_4(s, event, s', s_node, node);

                lemma_pred_4_1_b_new_helper_transpose_to_new_s_multiple(s, event, s', s_node, node);

                lemma_pred_4_1_b(s, event, s');
                lemma_pred_4_1_c(s, event, s');

                lemma_inv_sequence_attestation_duties_to_be_served_orderd(s, event, s');

                assert inv_g_b_body_body_new(s', node, s_node);
                assert inv_g_d_a_body_body(s', node, s_node);
                assert inv_g_a_ii_a_body_body(s', node, s_node);
                assert inv_g_iii_b_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_g_a_iii_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node);
                assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert pred_4_1_b(s');
                assert pred_4_1_c(s');             
                assert inv_g_a_iv_a_body_body(s', node, s_node);
                assert is_sequence_attestation_duties_to_be_served_orderd(s');

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lemma_ServeAttstationDuty(s, event, s');
                        lemma_inv_g_iii_b_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_g_iii_b_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        lemma_NonServeAttstationDuty(s, event, s');
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lemma_pred_4_1_g_iii_helper5(s, event, s');                 
                        lemma_inv_g_iii_b_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_g_iii_b_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                        
               
                   
                    case ReceviedAttesttionShare(attestation_share) =>
                        lemma_NonServeAttstationDuty(s, event, s'); 
                        lemma_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        lemma_inv_g_iii_b_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_iii_b_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  
                        

                    case ImportedNewBlock(block) => 
                        lemma_NonServeAttstationDuty(s, event, s');
                        var s_node2 := add_block_to_bn(s_node, nodeEvent.block);
                        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node, s_node2);
                        lemma_inv_g_iii_b_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_g_iii_b_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                     
                    
                 
                    case ResendAttestationShares => 
                        lemma_NonServeAttstationDuty(s, event, s');
                        lemma_f_resend_attestation_share_constants(s_node, s'_node);
                        lemma_inv_g_iii_b_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_iii_b_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  

                    case NoEvent => 
                        lemma_NonServeAttstationDuty(s, event, s');
                        assert s_node == s'_node; 
                        lemma_inv_g_iii_b_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_iii_b_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                          
                }
                // assert inv_g_iii_b_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  
        }
    }      

    lemma lemma_inv_g_iii_b_helper_easy_2(
        s': DVState
    )
    requires forall hn |
                        && hn in s'.honest_nodes_states.Keys   
                    :: inv_g_iii_b_body_body(s', hn, s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served); 
    ensures pred_4_1_g_iii_b(s')
    {

    }                 

    lemma lemma_4_1_g_iii_b(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEvent(s, event, s')
    requires lemma_pred_4_1_b_new_precond(s)
    ensures pred_4_1_g_iii_b(s');  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lemma_4_1_g_iii_b_helper_honest(s, event, s');
                   
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_g_iii_b_body_body(s', hn, s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lemma_pred_4_1_b_new_helper_transpose_to_new_s_multiple(s, event, s', s.honest_nodes_states[hn], hn);
                        lemma_inv_g_iii_b_helper_easy(s', event, s.honest_nodes_states[hn], s'.honest_nodes_states[hn], hn);
                    }
                }  

                lemma_inv_g_iii_b_helper_easy_2(s');
                         
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_g_iii_b_body_body(s', hn, s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served); 
                {
                    // if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lemma_pred_4_1_b_new_helper_transpose_to_new_s_multiple(s, event, s', s.honest_nodes_states[hn], hn);
                        lemma_inv_g_iii_b_helper_easy(s', event, s.honest_nodes_states[hn], s'.honest_nodes_states[hn], hn);
                    }
                }     
                assert pred_4_1_g_iii_b(s');  

        }
    }    

    lemma lemma_inv_g_d_a_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state   
    requires index_next_attestation_duty_to_be_served > 0    
    requires inv_g_d_a_body_body(dvn, n, process)
    ensures inv_g_d_a_body_body(dvn, n, s');
    {
        var new_p := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
        );

        lemma_inv_g_d_a_f_check_for_next_queued_duty(new_p, s', dvn, n);
    }    

    lemma lemma_inv_g_d_a_f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(process, id, decided_attestation_data).state
    requires inv_g_d_a_body_body(dvn, n, process)
    ensures inv_g_d_a_body_body(dvn, n, s'); 
    {
        // TODO: Remove below by changing spec
        assume id == process.current_attestation_duty.safe_get().slot;        
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

        lemma_inv_g_d_a_f_check_for_next_queued_duty(s_mod, s', dvn, n);             
    }  

    lemma lemma_inv_g_d_a_f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires inv_g_d_a_body_body(dvn, n, process)
    requires pred_4_1_b(dvn)
    requires pred_4_1_c(dvn)
    ensures inv_g_d_a_body_body(dvn, n, s');
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

        lemma_f_listen_for_new_imported_blocks_helper_1(
            dvn,
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
            
            lemma_inv_g_d_a_f_check_for_next_queued_duty(s_mod, s', dvn, n);   
        }      
    }      


    lemma lemma_inv_g_d_a_f_check_for_next_queued_duty(
        process: DVCNodeState,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state  
    requires inv_g_d_a_body_body(dvn, n, process)
    ensures inv_g_d_a_body_body(dvn, n, s')
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

                lemma_inv_g_d_a_f_check_for_next_queued_duty(s_mod, s', dvn, n );
            }
            else 
            {        

                assert inv_g_d_a_body_body(dvn, n, s');

            }
        } 
        else 
        {
        }       
    } 

    lemma lemma_inv_g_d_a_helper_honest(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEvent(s, event, s')   
    requires lemma_pred_4_1_b_new_precond(s)  
    requires event.HonestNodeTakingStep?
    ensures inv_g_d_a_body_body(s', event.node, s'.honest_nodes_states[event.node]); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                // lemma_pred_4_1_g_iii_helper3a(s, event, s', s_node, node);
                lemma_pred_4_1_g_iii_helper3c(s, event, s', s_node, node);
                // lemma_pred_4_1_b_new_helper_transpose_to_new_s_1(s, event, s', s_node, node);
                // lemma_pred_4_1_b_new_helper_transpose_to_new_s_2(s, event, s', s_node, node);
                // lemma_pred_4_1_b_new_helper_transpose_to_new_s_3(s, event, s', s_node, node);
                // lemma_pred_4_1_b_new_helper_transpose_to_new_s_4(s, event, s', s_node, node);

                // lemma_pred_4_1_b_new_helper_transpose_to_new_s_multiple(s, event, s', s_node, node);

                lemma_pred_4_1_b(s, event, s');
                lemma_pred_4_1_c(s, event, s');

                // lemma_inv_sequence_attestation_duties_to_be_served_orderd(s, event, s');

                // assert inv_g_b_body_body_new(s', node, s_node);
                assert inv_g_d_a_body_body(s', node, s_node);
                // assert inv_g_a_ii_a_body_body(s', node, s_node);
                // assert inv_g_iii_b_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                // assert inv_g_a_iii_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                // assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node);
                // assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);
                assert pred_4_1_b(s');
                assert pred_4_1_c(s');             
                // assert inv_g_a_iv_a_body_body(s', node, s_node);
                // assert is_sequence_attestation_duties_to_be_served_orderd(s');

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lemma_ServeAttstationDuty(s, event, s');
                        lemma_inv_g_d_a_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_g_d_a_body_body(s', node, s'_node);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        lemma_NonServeAttstationDuty(s, event, s');
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lemma_pred_4_1_g_iii_helper5(s, event, s');                 
                        lemma_inv_g_d_a_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_g_d_a_body_body(s', node, s'_node);                        
               
                   
                    case ReceviedAttesttionShare(attestation_share) =>
                        lemma_NonServeAttstationDuty(s, event, s'); 
                        lemma_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        // lemma_inv_g_d_a_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_d_a_body_body(s', node, s'_node);  
                        

                    case ImportedNewBlock(block) => 
                        lemma_NonServeAttstationDuty(s, event, s');
                        var s_node2 := add_block_to_bn(s_node, nodeEvent.block);
                        lemma_inv_g_d_a_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_g_d_a_body_body(s', node, s'_node);                     
                    
                 
                    case ResendAttestationShares => 
                        lemma_NonServeAttstationDuty(s, event, s');
                        lemma_f_resend_attestation_share_constants(s_node, s'_node);
                        // lemma_inv_g_d_a_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_d_a_body_body(s', node, s'_node);  

                    case NoEvent => 
                        lemma_NonServeAttstationDuty(s, event, s');
                        assert s_node == s'_node; 
                        // lemma_inv_g_d_a_helper_easy(s', event, s_node, s'_node, node );
                        assert inv_g_d_a_body_body(s', node, s'_node);                          
                }
                // assert inv_g_d_a_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  
        }
    }     

    lemma lemma_inv_g_d_a(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEvent(s, event, s')
    requires lemma_pred_4_1_b_new_precond(s)
    ensures inv_g_d_a(s');  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lemma_inv_g_d_a_helper_honest(s, event, s');
                   
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_g_d_a_body_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lemma_pred_4_1_g_iii_helper3c(s, event, s', s.honest_nodes_states[hn], hn);
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
                        lemma_pred_4_1_g_iii_helper3c(s, event, s', s.honest_nodes_states[hn], hn);
                    }
                }  
                assert inv_g_d_a(s');

        }
    }  

    lemma lemma_inv_attestation_duty_queue_is_ordered_3_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state   
    requires index_next_attestation_duty_to_be_served > 0    
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process) 
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, process, index_next_attestation_duty_to_be_served-1)  
    requires is_sequence_attestation_duties_to_be_served_orderd(dvn);
    requires 
                var an' := dvn.sequence_attestation_duties_to_be_served[index_next_attestation_duty_to_be_served-1];
                && an'.attestation_duty == attestation_duty
                && an'.node == n
    ensures inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, s');
    {
        var new_p := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
        );

        if |process.attestation_duties_queue| == 0 
        {
            assert inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, new_p);  
        }
        else 
        {
            forall i: nat, k, l, t  |
                inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                    dvn,
                    n, 
                    new_p,
                    i,
                    k, 
                    l, 
                    t
                )
            ensures 
                new_p.attestation_duties_queue[i-1].slot == dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot      
            {
                // assert process.attestation_duties_queue != [];
                assert i > 0;


                if i != |new_p.attestation_duties_queue| - 1
                {
                    assert inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                        dvn,
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

                    assert new_p.attestation_duties_queue[i-1].slot <= dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;

                    assert inv_attestation_duty_queue_is_ordered_4_body_body_premise(dvn, n, process, t, index_next_attestation_duty_to_be_served-1);

                    assert new_p.attestation_duties_queue[i-1].slot == dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;
                }

            }   
        }        

        lemma_inv_attestation_duty_queue_is_ordered_3_f_check_for_next_queued_duty(new_p, s', dvn, n);
    }     

    lemma lemma_inv_attestation_duty_queue_is_ordered_3_f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(process, id, decided_attestation_data).state
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process)
    ensures inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, s'); 
    {
        // TODO: Remove below by changing spec
        assume id == process.current_attestation_duty.safe_get().slot;        
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

        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process, s_mod);
        lemma_inv_attestation_duty_queue_is_ordered_3_f_check_for_next_queued_duty(s_mod, s', dvn, n);             
    }  

    lemma lemma_inv_attestation_duty_queue_is_ordered_3_f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process)
    ensures inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, s')
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
            
            lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process, s_mod);
            lemma_inv_attestation_duty_queue_is_ordered_3_f_check_for_next_queued_duty(s_mod, s', dvn, n);
        } 
        else 
        {
            lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process, s');           
        }     
    }           

    lemma lemma_inv_attestation_duty_queue_is_ordered_3_f_check_for_next_queued_duty(
        process: DVCNodeState,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state  
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process)
    ensures inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, s')
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

                lemma3_inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process, s_mod);
                lemma_inv_attestation_duty_queue_is_ordered_3_f_check_for_next_queued_duty(s_mod, s', dvn, n );
            }
            else 
            {        
                lemma3_inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process, s');
                assert inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, s');

            }
        } 
        else 
        {
            assert inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, s');
        }       
    }  

    lemma lemma_inv_attestation_duty_queue_is_ordered_3_honest(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
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

                lemma_pred_4_1_b_new_helper_transpose_to_new_s_3(s, event, s', s_node, node);
                lemma_inv_sequence_attestation_duties_to_be_served_orderd(s, event, s');

                assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node);
                assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lemma_ServeAttstationDuty(s, event, s');
                        lemma_inv_attestation_duty_queue_is_ordered_3_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s'_node);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        lemma_NonServeAttstationDuty(s, event, s');
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lemma_inv_attestation_duty_queue_is_ordered_3_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s'_node);                        
               
                   
                    case ReceviedAttesttionShare(attestation_share) =>
                        lemma_NonServeAttstationDuty(s, event, s'); 
                        lemma_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node, s'_node);
                        assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s'_node);  
                        

                    case ImportedNewBlock(block) => 
                        lemma_NonServeAttstationDuty(s, event, s');
                        var s_node2 := add_block_to_bn(s_node, nodeEvent.block);
                        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node, s_node2);
                        lemma_inv_attestation_duty_queue_is_ordered_3_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s'_node);                     
                    
                 
                    case ResendAttestationShares => 
                        lemma_NonServeAttstationDuty(s, event, s');
                        lemma_f_resend_attestation_share_constants(s_node, s'_node);
                        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node, s'_node);
                        assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s'_node); 

                    case NoEvent => 
                        lemma_NonServeAttstationDuty(s, event, s');
                        assert s_node == s'_node; 
                        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s_node, s'_node);
                        assert inv_attestation_duty_queue_is_ordered_3_body_body(s', node, s'_node);                          
                }                
        }
    }         


    lemma lemma_inv_attestation_duty_queue_is_ordered_3(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
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
                lemma_inv_attestation_duty_queue_is_ordered_3_honest(s, event, s');
                   
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_attestation_duty_queue_is_ordered_3_body_body(s', hn, s'.honest_nodes_states[hn]); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lemma_pred_4_1_b_new_helper_transpose_to_new_s_3(s, event, s', s.honest_nodes_states[hn], hn);
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
                        lemma_pred_4_1_b_new_helper_transpose_to_new_s_3(s, event, s', s.honest_nodes_states[hn], hn);
                        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(s', hn, s.honest_nodes_states[hn], s'.honest_nodes_states[hn]);
                    }
                }   

        }
    }    

    lemma lemma_inv_attestation_duty_queue_is_ordered_4_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state   
    requires index_next_attestation_duty_to_be_served > 0    
    // requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process) 
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, process, index_next_attestation_duty_to_be_served-1)  
    requires is_sequence_attestation_duties_to_be_served_orderd(dvn);
    requires 
                var an' := dvn.sequence_attestation_duties_to_be_served[index_next_attestation_duty_to_be_served-1];
                && an'.attestation_duty == attestation_duty
                && an'.node == n
    ensures inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, s', index_next_attestation_duty_to_be_served);
    {
        var new_p := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
        );

        assert inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, new_p, index_next_attestation_duty_to_be_served);         

        lemma_inv_attestation_duty_queue_is_ordered_4_f_check_for_next_queued_duty(new_p, s', dvn, n, index_next_attestation_duty_to_be_served);
    } 

    lemma lemma_inv_attestation_duty_queue_is_ordered_4_f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(process, id, decided_attestation_data).state
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    ensures inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, s', index_next_attestation_duty_to_be_served); 
    {
        // TODO: Remove below by changing spec
        assume id == process.current_attestation_duty.safe_get().slot;        
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

        lemma2_inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, process, s_mod, index_next_attestation_duty_to_be_served);
        lemma_inv_attestation_duty_queue_is_ordered_4_f_check_for_next_queued_duty(s_mod, s', dvn, n, index_next_attestation_duty_to_be_served);             
    }       

    lemma lemma_inv_attestation_duty_queue_is_ordered_4_f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    ensures inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, s', index_next_attestation_duty_to_be_served)
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
            
            lemma2_inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, process, s_mod, index_next_attestation_duty_to_be_served);
            lemma_inv_attestation_duty_queue_is_ordered_4_f_check_for_next_queued_duty(s_mod, s', dvn, n, index_next_attestation_duty_to_be_served);
        } 
        else 
        {
            lemma2_inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, process, s', index_next_attestation_duty_to_be_served);           
        }     
    }                 
    
    lemma lemma_inv_attestation_duty_queue_is_ordered_4_f_check_for_next_queued_duty(
        process: DVCNodeState,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state  
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)  
    ensures inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, s', index_next_attestation_duty_to_be_served)      
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

                lemma3_inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, process, s_mod, index_next_attestation_duty_to_be_served);
                lemma_inv_attestation_duty_queue_is_ordered_4_f_check_for_next_queued_duty(s_mod, s', dvn, n , index_next_attestation_duty_to_be_served);
            }
            else 
            {
                var new_process := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..]
                );   

                var queue_head := process.attestation_duties_queue[0];      
                lemma3_inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, process, new_process, index_next_attestation_duty_to_be_served);                 


                // assert inv_g_a_ii_a_body_body(dvn, n, s');

            }
        } 
        else 
        {
            lemma2_inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, process, s', index_next_attestation_duty_to_be_served);
        }       
    }     

    lemma lemma_inv_attestation_duty_queue_is_ordered_4_honest(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
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

                lemma_pred_4_1_b_new_helper_transpose_to_new_s_3(s, event, s', s_node, node);
                lemma_inv_sequence_attestation_duties_to_be_served_orderd(s, event, s');

                assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s.index_next_attestation_duty_to_be_served);

                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lemma_ServeAttstationDuty(s, event, s');
                        lemma_inv_attestation_duty_queue_is_ordered_4_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                     
                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        lemma_NonServeAttstationDuty(s, event, s');
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lemma_inv_attestation_duty_queue_is_ordered_4_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                        
               
                   
                    case ReceviedAttesttionShare(attestation_share) =>
                        lemma_NonServeAttstationDuty(s, event, s'); 
                        lemma_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        lemma2_inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s'_node, s'.index_next_attestation_duty_to_be_served);
                        assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);  
                        

                    case ImportedNewBlock(block) => 
                        lemma_NonServeAttstationDuty(s, event, s');
                        var s_node2 := add_block_to_bn(s_node, nodeEvent.block);
                        lemma2_inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s_node2, s'.index_next_attestation_duty_to_be_served);
                        lemma_inv_attestation_duty_queue_is_ordered_4_f_listen_for_new_imported_blocks(
                            s_node2,
                            block,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                     
                    
                 
                    case ResendAttestationShares => 
                        lemma_NonServeAttstationDuty(s, event, s');
                        lemma_f_resend_attestation_share_constants(s_node, s'_node);
                        lemma2_inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s'_node, s'.index_next_attestation_duty_to_be_served);
                        assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served); 

                    case NoEvent => 
                        lemma_NonServeAttstationDuty(s, event, s');
                        assert s_node == s'_node; 
                        lemma2_inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s_node, s'_node, s'.index_next_attestation_duty_to_be_served);
                        assert inv_attestation_duty_queue_is_ordered_4_body_body(s', node, s'_node, s'.index_next_attestation_duty_to_be_served);                          
                }                
        }
    }   

    lemma lemma_inv_attestation_duty_queue_is_ordered_4_helper_other_node(
        s: DVState,
        event: DV.Event,
        s': DVState,
        hn: BLSPubkey
    )
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
        lemma_pred_4_1_b_new_helper_transpose_to_new_s_3(s, event, s', s.honest_nodes_states[hn], hn);

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


    lemma lemma_inv_attestation_duty_queue_is_ordered_4(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
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
                lemma_inv_attestation_duty_queue_is_ordered_4_honest(s, event, s');
                   
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_attestation_duty_queue_is_ordered_4_body_body(s', hn, s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served); 
                {
                    if hn != node 
                    {
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        lemma_pred_4_1_b_new_helper_transpose_to_new_s_3(s, event, s', s.honest_nodes_states[hn], hn);
                        if event.event.ServeAttstationDuty?
                        {
                            lemma_inv_attestation_duty_queue_is_ordered_4_helper_other_node(
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
                    lemma_pred_4_1_b_new_helper_transpose_to_new_s_3(s, event, s', s.honest_nodes_states[hn], hn);
                    lemma2_inv_attestation_duty_queue_is_ordered_4_body_body(s', hn, s.honest_nodes_states[hn], s'.honest_nodes_states[hn], s'.index_next_attestation_duty_to_be_served);
                }  

        }
    }    

    lemma lemma_inv_g_a_iii_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state   
    requires index_next_attestation_duty_to_be_served > 0    
    requires inv_g_a_iii_body_body(dvn, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_g_a_ii_a_body_body(dvn, n, process)
    requires inv_g_d_a_body_body(dvn, n, process)
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)  
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process)  
    requires is_sequence_attestation_duties_to_be_served_orderd(dvn);
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)
    requires inv_g_b_body_body_new(dvn, n, process)
    requires inv_g_a_iv_a_body_body(dvn, n, process)    
    requires 
                var an' := dvn.sequence_attestation_duties_to_be_served[index_next_attestation_duty_to_be_served-1];
                && an'.attestation_duty == attestation_duty
                && an'.node == n
    ensures inv_g_a_iii_body_body(dvn, n, s', index_next_attestation_duty_to_be_served);
    {
        var new_p := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
        );

        if |process.attestation_duties_queue| == 0 
        {
            assert inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, new_p);  
        }
        else 
        {
            forall i: nat, k, l, t  |
                inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                    dvn,
                    n, 
                    new_p,
                    i,
                    k, 
                    l, 
                    t
                )
            ensures 
                new_p.attestation_duties_queue[i-1].slot == dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot      
            {
                // assert process.attestation_duties_queue != [];
                assert i > 0;


                if i != |new_p.attestation_duties_queue| - 1
                {
                    assert inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                        dvn,
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

                    assert new_p.attestation_duties_queue[i-1].slot <= dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;

                    assert inv_attestation_duty_queue_is_ordered_4_body_body_premise(dvn, n, process, t, index_next_attestation_duty_to_be_served-1);

                    assert new_p.attestation_duties_queue[i-1].slot == dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;
                }

            }   
        }



        lemma_inv_g_a_iii_f_check_for_next_queued_duty(new_p, s', dvn, n, index_next_attestation_duty_to_be_served);
    } 

    lemma lemma_inv_g_b_body_body_new_intermediate_f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s_mod: DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )  
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires inv_g_b_body_body_new(dvn, n, process)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process)   
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)    
    requires dvn.consensus_on_attestation_data[id].decided_value.isPresent()
    requires dvn.consensus_on_attestation_data[id].decided_value.safe_get() ==  decided_attestation_data 
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
    ensures inv_g_b_body_body_new(dvn, n, s_mod);
    {

        assert s_mod.attestation_duties_queue == process.attestation_duties_queue;

        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process, s_mod);

        assert inv_g_b_body_body_new(dvn, n, s_mod);
    }

    lemma lemma_inv_g_b_body_body_new_intermediate_f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock,        
        s_mod: DVCNodeState,
        dvn: DVState,
        n: BLSPubkey
    )  
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires inv_g_b_body_body_new(dvn, n, process)
    requires inv_g_d_a_body_body(dvn, n, process)
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)
    requires pred_4_1_b(dvn)
    requires pred_4_1_c(dvn)         
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
    ensures inv_g_b_body_body_new(dvn, n, s_mod);
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

            // lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process, s_mod);


            lemma_f_listen_for_new_imported_blocks_helper_1(
                dvn,
                process,
                block,
                new_consensus_instances_already_decided
            );

            assert 
                && dvn.consensus_on_attestation_data[new_process.current_attestation_duty.safe_get().slot].decided_value.isPresent()
                && dvn.consensus_on_attestation_data[new_process.current_attestation_duty.safe_get().slot].decided_value.safe_get() == decided_attestation_data
            ;                        

            assert inv_g_b_body_body_new(dvn, n, s_mod);

    }    

    lemma lemma_inv_g_a_iii_f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(process, id, decided_attestation_data).state
    requires inv_g_a_iii_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_a_ii_a_body_body(dvn, n, process)
    requires inv_g_d_a_body_body(dvn, n, process)
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)  
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process)  


    requires inv_g_b_body_body_new(dvn, n, process)
    requires inv_g_a_iv_a_body_body(dvn, n, process)
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)

    requires dvn.consensus_on_attestation_data[id].decided_value.isPresent()
    requires dvn.consensus_on_attestation_data[id].decided_value.safe_get() ==  decided_attestation_data 
    ensures inv_g_a_iii_body_body(dvn, n, s', index_next_attestation_duty_to_be_served)
    {
        // TODO: Remove below by changing spec
        assume id == process.current_attestation_duty.safe_get().slot;        
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

        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process, s_mod);

        lemma_inv_g_b_body_body_new_intermediate_f_att_consensus_decided(process, id, decided_attestation_data, s_mod, dvn, n, index_next_attestation_duty_to_be_served);

        assert inv_g_b_body_body_new(dvn, n, s_mod);

        assert get_upperlimit_decided_instances(s_mod) == process.latest_attestation_duty.safe_get().slot + 1;

        if
            &&  |s_mod.attestation_duties_queue| > 0 
            &&   !s_mod.current_attestation_duty.isPresent()        
        {
            forall an |
                && an in dvn.sequence_attestation_duties_to_be_served.Values 
                && an.node == n 
                && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot   
            ensures      
                    var slot := an.attestation_duty.slot;
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                        ;                        
            {
                var slot := an.attestation_duty.slot;

                if slot > s_mod.latest_attestation_duty.safe_get().slot
                {
                    assert 
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                        ;                    
                }
                else if slot == s_mod.latest_attestation_duty.safe_get().slot
                {
                    assert 
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                        ;                         
                }
                else 
                {
                    assert slot < s_mod.latest_attestation_duty.safe_get().slot;
                    assert 
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                        ;                           
                }

            }
        }
        assert inv_g_a_ii_a_body_body(dvn, n, s_mod);

        assert inv_g_a_iii_body_body(dvn, n, s_mod, index_next_attestation_duty_to_be_served);        


        lemma_inv_g_a_iii_f_check_for_next_queued_duty(s_mod, s', dvn, n, index_next_attestation_duty_to_be_served);             
    }      

    lemma lemma_inv_g_a_iii_f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires inv_g_a_iii_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_a_ii_a_body_body(dvn, n, process)
    requires inv_g_d_a_body_body(dvn, n, process)
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)  
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process)

    requires pred_inv_current_latest_attestation_duty_match_body_body(process)
    requires inv_g_b_body_body_new(dvn, n, process)
    requires inv_g_a_iv_a_body_body(dvn, n, process)

    requires pred_4_1_b(dvn)
    requires pred_4_1_c(dvn)    

    ensures inv_g_a_iii_body_body(dvn, n, s', index_next_attestation_duty_to_be_served)
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

            lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process, s_mod);

            lemma_f_listen_for_new_imported_blocks_helper_1(
                dvn,
                process,
                block,
                new_consensus_instances_already_decided
            );

            assert inv_g_d_a_body_body(dvn, n, s_mod);    

            lemma_inv_g_b_body_body_new_intermediate_f_listen_for_new_imported_blocks(
                process, block, s_mod, dvn, n
            );

            assert inv_g_b_body_body_new(dvn, n, s_mod);


            if
                &&  |s_mod.attestation_duties_queue| > 0 
                &&   !s_mod.current_attestation_duty.isPresent()        
            {
                forall an |
                    && an in dvn.sequence_attestation_duties_to_be_served.Values 
                    && an.node == n 
                    && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot   
                ensures      
                        var slot := an.attestation_duty.slot;
                            && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                        
                {
                    var slot := an.attestation_duty.slot;

                    if slot > s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                    
                    }
                    else if slot == s_mod.latest_attestation_duty.safe_get().slot
                    {
                        assert 
                            && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                         
                    }
                    else 
                    {
                        assert slot < s_mod.latest_attestation_duty.safe_get().slot;
                        assert 
                            && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                            ;                           
                    }

                }
            }
            assert inv_g_a_ii_a_body_body(dvn, n, s_mod);                 
                   
            lemma_inv_g_a_iii_f_check_for_next_queued_duty(s_mod, s', dvn, n, index_next_attestation_duty_to_be_served);                    
        }        
    }           

    lemma lemma_inv_g_a_iii_f_check_for_next_queued_duty(
        process: DVCNodeState,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state  
    requires inv_g_a_iii_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_g_a_ii_a_body_body(dvn, n, process)
    requires inv_g_d_a_body_body(dvn, n, process)
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)  
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process)

    requires pred_inv_current_latest_attestation_duty_match_body_body(process)
    requires inv_g_b_body_body_new(dvn, n, process)
    requires inv_g_a_iv_a_body_body(dvn, n, process)

    ensures inv_g_a_iii_body_body(dvn, n, s', index_next_attestation_duty_to_be_served)
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
                        && var an := dvn.sequence_attestation_duties_to_be_served[i];
                        && an.node == n 
                        && inv_g_a_iii_body_body_helper(s_mod, an.attestation_duty.slot)
                    ensures 
                        var an := dvn.sequence_attestation_duties_to_be_served[i];
                        var slot := an.attestation_duty.slot;   
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db      
                        ;                                           
                    {
                        var an := dvn.sequence_attestation_duties_to_be_served[i];
                        var slot := an.attestation_duty.slot;

                        if slot < queue_head.slot 
                        {
                            if  !process.current_attestation_duty.isPresent()
                            {
                                assert
                                && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                                && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db      
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
                                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db      
                                        ;                                             
                                    }
                                    else 
                                    {
                                        assert slot > process.latest_attestation_duty.safe_get().slot;
                                        assert
                                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db      
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
                                dvn,
                                n, 
                                process,
                                i,
                                index_next_attestation_duty_to_be_served
                            );                            

                            var last := seq_last(process.attestation_duties_queue);
                            assert last.slot == dvn.sequence_attestation_duties_to_be_served[i].attestation_duty.slot;

                            assert
                            && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                            && process.future_att_consensus_instances_already_decided[slot] == dvn.consensus_on_attestation_data[slot].decided_value.safe_get()  
                            ;               

                            assert 
                            && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db   
                            ;                                       
                            // assert last.slot == queue_head.slot;

                        }

              
                    }
                }
                assert inv_g_a_iii_body_body(dvn, n, s_mod, index_next_attestation_duty_to_be_served);

                if  && |s_mod.attestation_duties_queue| > 0 
                    &&   !s_mod.current_attestation_duty.isPresent()
                {
                  
                    forall an |
                        && an in dvn.sequence_attestation_duties_to_be_served.Values 
                        && an.node == n 
                        && an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot
                    ensures 
                        var slot := an.attestation_duty.slot;
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                    ;                          
                    {
                        var slot := an.attestation_duty.slot;
                   
                        if an.attestation_duty.slot < process.attestation_duties_queue[0].slot  
                        {
                            assert 
                                && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                                && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                            ;
                        }
                        else 
                        {
                            var t :|  dvn.sequence_attestation_duties_to_be_served[t] == an;
                            assert process.attestation_duties_queue[0] in process.attestation_duties_queue;
                            var i :|  
                                    && dvn.sequence_attestation_duties_to_be_served[i].node == n 
                                    && dvn.sequence_attestation_duties_to_be_served[i].attestation_duty == process.attestation_duties_queue[0];
                            assert process.attestation_duties_queue[1] in process.attestation_duties_queue;
                            var j :|  
                                    && dvn.sequence_attestation_duties_to_be_served[j].node == n 
                                    && dvn.sequence_attestation_duties_to_be_served[j].attestation_duty == process.attestation_duties_queue[1];   

                            lemma_inv_attestation_duty_queue_is_ordered_3_body_body(
                                dvn,
                                n,
                                process,
                                1,
                                i,
                                j,
                                t
                            ); 

                        
                            assert 
                                && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                                && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                            ;
                            
                        }
                    }                  
                }
                assert inv_g_a_ii_a_body_body(dvn, n, s_mod);     

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
                        && an in dvn.sequence_attestation_duties_to_be_served.Values 
                        && an.node == n 
                        && s_mod.latest_attestation_duty.safe_get().slot < an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot   
                    ensures 
                        var slot := an.attestation_duty.slot;
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db                          
                    {
                        var slot := an.attestation_duty.slot;

                        assert process.latest_attestation_duty.safe_get().slot < an.attestation_duty.slot;

                        if slot < process.attestation_duties_queue[0].slot
                        {

                        }
                        else 
                        {
                            var t :|  dvn.sequence_attestation_duties_to_be_served[t] == an;
                            assert process.attestation_duties_queue[0] in process.attestation_duties_queue;
                            var k :|  
                                    && dvn.sequence_attestation_duties_to_be_served[k].node == n 
                                    && dvn.sequence_attestation_duties_to_be_served[k].attestation_duty == process.attestation_duties_queue[0];
                            assert process.attestation_duties_queue[1] in process.attestation_duties_queue;
                            var l :|  
                                    && dvn.sequence_attestation_duties_to_be_served[l].node == n 
                                    && dvn.sequence_attestation_duties_to_be_served[l].attestation_duty == process.attestation_duties_queue[1];   

                            lemma_inv_attestation_duty_queue_is_ordered_3_body_body(
                                dvn,
                                n,
                                process,
                                1,
                                k,
                                l,
                                t
                            ); 

                        
                            assert 
                                && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                                && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                            ;
                            
                        }
                    }               
                }  
                assert inv_g_a_iv_a_body_body(dvn, n, s_mod);         


                lemma3_inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process, s_mod);


                lemma_inv_g_a_iii_f_check_for_next_queued_duty(s_mod, s', dvn, n , index_next_attestation_duty_to_be_served);
            }
            else 
            {
                var new_process := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..]
                );          

                assert inv_g_a_iii_body_body(dvn, n, s', index_next_attestation_duty_to_be_served);

            }
        } 
        else 
        {
            // assert inv_g_b_body_body_new(dvn, n, s');
        }       
    }  
    
    lemma lemma_inv_g_a_iv_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state   
    requires index_next_attestation_duty_to_be_served > 0    
    requires inv_g_a_iv_a_body_body(dvn, n, process)
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process)
    requires inv_g_d_a_body_body(dvn, n, process)

    requires inv_g_a_iii_body_body(dvn, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_attestation_duty_queue_is_ordered_4_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)  
    requires is_sequence_attestation_duties_to_be_served_orderd(dvn);
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)

    requires 
                var an' := dvn.sequence_attestation_duties_to_be_served[index_next_attestation_duty_to_be_served-1];
                && an'.attestation_duty == attestation_duty
                && an'.node == n
    ensures inv_g_a_iv_a_body_body(dvn, n, s') 
    {
        var new_p := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
        );

        if |process.attestation_duties_queue| == 0 
        {
            assert inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, new_p);  
        }
        else 
        {
            forall i: nat, k, l, t  |
                inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                    dvn,
                    n, 
                    new_p,
                    i,
                    k, 
                    l, 
                    t
                )
            ensures 
                new_p.attestation_duties_queue[i-1].slot == dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot      
            {
                // assert process.attestation_duties_queue != [];
                assert i > 0;


                if i != |new_p.attestation_duties_queue| - 1
                {
                    assert inv_attestation_duty_queue_is_ordered_3_body_body_premise(
                        dvn,
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

                    assert new_p.attestation_duties_queue[i-1].slot <= dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;

                    assert inv_attestation_duty_queue_is_ordered_4_body_body_premise(dvn, n, process, t, index_next_attestation_duty_to_be_served-1);

                    assert new_p.attestation_duties_queue[i-1].slot == dvn.sequence_attestation_duties_to_be_served[t].attestation_duty.slot;
                }

            }   
        }

        lemma_inv_g_a_iv_f_check_for_next_queued_duty(new_p, s', dvn, n, index_next_attestation_duty_to_be_served);
    }          

    lemma lemma_inv_g_a_iv_f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(process, id, decided_attestation_data).state
    requires inv_g_a_iv_a_body_body(dvn, n, process)
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process)
    requires inv_g_d_a_body_body(dvn, n, process)

    requires dvn.consensus_on_attestation_data[id].decided_value.isPresent()
    requires dvn.consensus_on_attestation_data[id].decided_value.safe_get() ==  decided_attestation_data 
    ensures inv_g_a_iv_a_body_body(dvn, n, s')       
    {
        // TODO: Remove below by changing spec
        assume id == process.current_attestation_duty.safe_get().slot;        
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

        lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process, s_mod);

        lemma_inv_g_a_iv_f_check_for_next_queued_duty(s_mod, s', dvn, n, index_next_attestation_duty_to_be_served);             
    }        

    lemma lemma_inv_g_a_iv_f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state  
    requires inv_g_a_iv_a_body_body(dvn, n, process)
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process)
    requires inv_g_d_a_body_body(dvn, n, process)
    requires pred_4_1_b(dvn)
    requires pred_4_1_c(dvn)    
    ensures inv_g_a_iv_a_body_body(dvn, n, s')   
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

            lemma2_inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process, s_mod);

            lemma_f_listen_for_new_imported_blocks_helper_1(
                dvn,
                process,
                block,
                new_consensus_instances_already_decided
            );

            assert inv_g_d_a_body_body(dvn, n, s_mod);    
                   
            lemma_inv_g_a_iv_f_check_for_next_queued_duty(s_mod, s', dvn, n, index_next_attestation_duty_to_be_served);                    
        }        
    }        

    lemma lemma_inv_g_a_iv_f_check_for_next_queued_duty(
        process: DVCNodeState,
        s': DVCNodeState,
        dvn: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state  
    requires inv_g_a_iv_a_body_body(dvn, n, process)
    requires inv_g_iii_b_body_body(dvn, n, process, index_next_attestation_duty_to_be_served)
    requires inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process)
    requires inv_g_d_a_body_body(dvn, n, process)
    ensures inv_g_a_iv_a_body_body(dvn, n, s')
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
                        && an in dvn.sequence_attestation_duties_to_be_served.Values 
                        && an.node == n 
                        && s_mod.latest_attestation_duty.safe_get().slot < an.attestation_duty.slot < s_mod.attestation_duties_queue[0].slot   
                    ensures 
                        var slot := an.attestation_duty.slot;
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db                          
                    {
                        var slot := an.attestation_duty.slot;

                        assert process.latest_attestation_duty.safe_get().slot < an.attestation_duty.slot;

                        if slot < process.attestation_duties_queue[0].slot
                        {

                        }
                        else 
                        {
                            var t :|  dvn.sequence_attestation_duties_to_be_served[t] == an;
                            assert process.attestation_duties_queue[0] in process.attestation_duties_queue;
                            var k :|  
                                    && dvn.sequence_attestation_duties_to_be_served[k].node == n 
                                    && dvn.sequence_attestation_duties_to_be_served[k].attestation_duty == process.attestation_duties_queue[0];
                            assert process.attestation_duties_queue[1] in process.attestation_duties_queue;
                            var l :|  
                                    && dvn.sequence_attestation_duties_to_be_served[l].node == n 
                                    && dvn.sequence_attestation_duties_to_be_served[l].attestation_duty == process.attestation_duties_queue[1];   

                            lemma_inv_attestation_duty_queue_is_ordered_3_body_body(
                                dvn,
                                n,
                                process,
                                1,
                                k,
                                l,
                                t
                            ); 

                        
                            assert 
                                && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                                && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db     
                            ;
                            
                        }
                    }               
                }  
                assert inv_g_a_iv_a_body_body(dvn, n, s_mod);         


                lemma3_inv_attestation_duty_queue_is_ordered_3_body_body(dvn, n, process, s_mod);


                lemma_inv_g_a_iv_f_check_for_next_queued_duty(s_mod, s', dvn, n , index_next_attestation_duty_to_be_served);
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
                        && an in dvn.sequence_attestation_duties_to_be_served.Values 
                        && an.node == n 
                        && s'.latest_attestation_duty.safe_get().slot < an.attestation_duty.slot < s'.attestation_duties_queue[0].slot 
                    ensures
                        var slot := an.attestation_duty.slot;
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s'.attestation_slashing_db     
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
                                var t :|  dvn.sequence_attestation_duties_to_be_served[t] == an;
                                assert process.attestation_duties_queue[0] in process.attestation_duties_queue;
                                var k :|  
                                        && dvn.sequence_attestation_duties_to_be_served[k].node == n 
                                        && dvn.sequence_attestation_duties_to_be_served[k].attestation_duty == process.attestation_duties_queue[0];
                                assert process.attestation_duties_queue[1] in process.attestation_duties_queue;
                                var l :|  
                                        && dvn.sequence_attestation_duties_to_be_served[l].node == n 
                                        && dvn.sequence_attestation_duties_to_be_served[l].attestation_duty == process.attestation_duties_queue[1];   

                                lemma_inv_attestation_duty_queue_is_ordered_3_body_body(
                                    dvn,
                                    n,
                                    process,
                                    1,
                                    k,
                                    l,
                                    t
                                ); 

                            
                                assert 
                                    && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                                    && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s'.attestation_slashing_db     
                                ;
                                
                            }    
                            assert 
                                && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                                && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s'.attestation_slashing_db     
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
                                var t :|  dvn.sequence_attestation_duties_to_be_served[t] == an;
                                assert process.attestation_duties_queue[0] in process.attestation_duties_queue;
                                var k :|  
                                        && dvn.sequence_attestation_duties_to_be_served[k].node == n 
                                        && dvn.sequence_attestation_duties_to_be_served[k].attestation_duty == process.attestation_duties_queue[0];
                                assert process.attestation_duties_queue[1] in process.attestation_duties_queue;
                                var l :|  
                                        && dvn.sequence_attestation_duties_to_be_served[l].node == n 
                                        && dvn.sequence_attestation_duties_to_be_served[l].attestation_duty == process.attestation_duties_queue[1];   

                                lemma_inv_attestation_duty_queue_is_ordered_3_body_body(
                                    dvn,
                                    n,
                                    process,
                                    1,
                                    k,
                                    l,
                                    t
                                ); 

                            
                                assert 
                                    && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                                    && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s'.attestation_slashing_db     
                                ;
                                
                            }    
                            assert 
                                && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                                && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in s'.attestation_slashing_db     
                            ;                               
                        }
                    }
                }  

                assert inv_g_a_iv_a_body_body(dvn, n, s');         

            }
        } 
        else 
        {
            // assert inv_g_b_body_body_new(dvn, n, s');
        }       
    }       

}