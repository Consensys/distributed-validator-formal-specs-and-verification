include "../../../../common/commons.dfy"
include "../../common/attestation_creation_instrumented.dfy"
include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_attestation_creation.dfy"
include "../../../../specs/dvc/dvc_attestation_creation.dfy"

include "../../../common/helper_sets_lemmas.dfy"
include "../../../no_slashable_attestations/common/common_proofs.dfy"
include "../../../no_slashable_attestations/common/dvc_spec_axioms.dfy"

include "invs_dv_next_1.dfy"

include "../inv.dfy"

module Invs_DV_Next_3
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Spec
    import opened DV    
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Helper_Sets_Lemmas
    import opened Common_Proofs
    import opened Invs_DV_Next_1
    import DVC_Spec_NonInstr
    import opened DVC_Spec_Axioms

    predicate lem_ServeAttstationDuty2_predicate(
        s': DVState,
        index_next_attestation_duty_to_be_served: nat,
        attestation_duty: AttestationDuty,
        node: BLSPubkey
    )
    {
        && index_next_attestation_duty_to_be_served > 0
        && var an := s'.sequence_attestation_duties_to_be_served[index_next_attestation_duty_to_be_served - 1];

        && attestation_duty == an.attestation_duty
        && node == an.node    
    }    

    lemma lem_ServeAttstationDuty2_helper(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Types.Event,
        nodeOutputs: DVC_Spec.Outputs,
        s': DVState
    )
    requires NextHonestAfterAddingBlockToBn.requires(s, node, nodeEvent, nodeOutputs, s' );
    requires NextHonestAfterAddingBlockToBn(s, node, nodeEvent, nodeOutputs, s' );  
    requires nodeEvent.ServeAttstationDuty?
    ensures  s'.index_next_attestation_duty_to_be_served > 0

    ensures
            && lem_ServeAttstationDuty2_predicate(s', s'.index_next_attestation_duty_to_be_served, nodeEvent.attestation_duty, node )
            && s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
    {

        var s_node := s.honest_nodes_states[node];
        var s'_node := s'.honest_nodes_states[node];
        assert  NextHonestAfterAddingBlockToBn.requires(add_block_to_bn_with_event(s, node, nodeEvent), node, nodeEvent, nodeOutputs, s' );
        assert  NextHonestAfterAddingBlockToBn(add_block_to_bn_with_event(s, node, nodeEvent), node, nodeEvent, nodeOutputs, s' );
        // assert validNodeEvent(s, node, nodeEvent);


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

    // TODO: Rename to lem_ServeAttstationDuty
    lemma lem_ServeAttstationDuty2(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')    
    requires event.HonestNodeTakingStep?
    requires event.event.ServeAttstationDuty?
    ensures             s'.index_next_attestation_duty_to_be_served > 0

    ensures
            && lem_ServeAttstationDuty2_predicate(s', s'.index_next_attestation_duty_to_be_served, event.event.attestation_duty, event.node )
            && s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                assert  NextHonestAfterAddingBlockToBn.requires(add_block_to_bn_with_event(s, node, nodeEvent), node, nodeEvent, nodeOutputs, s' );
                assert  NextHonestAfterAddingBlockToBn(add_block_to_bn_with_event(s, node, nodeEvent), node, nodeEvent, nodeOutputs, s' );
                lem_ServeAttstationDuty2_helper(add_block_to_bn_with_event(s, node, nodeEvent), node, nodeEvent, nodeOutputs, s' );
        }        
    }    

    lemma lem_f_serve_attestation_duty_constants(
        s: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState
    )  
    requires f_serve_attestation_duty.requires(s, attestation_duty)
    requires s' == f_serve_attestation_duty(s, attestation_duty).state
    ensures s'.bn.attestations_submitted == s.bn.attestations_submitted      
    ensures s'.rcvd_attestation_shares == s.rcvd_attestation_shares
    ensures f_serve_attestation_duty(s, attestation_duty).outputs == getEmptyOuputs()
    {
        var s_mod := s.(
                attestation_duties_queue := s.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := s.all_rcvd_duties + {attestation_duty}
            );
        lem_f_check_for_next_queued_duty_constants(s_mod, s');
    }

    lemma lem_f_check_for_next_queued_duty_constants(
        s: DVCState,
        s': DVCState
    )
    requires f_check_for_next_queued_duty.requires(s)
    requires s' == f_check_for_next_queued_duty(s).state
    ensures s'.bn.attestations_submitted == s.bn.attestations_submitted
    ensures s'.rcvd_attestation_shares == s.rcvd_attestation_shares
    ensures f_check_for_next_queued_duty(s).outputs == getEmptyOuputs()
    decreases s.attestation_duties_queue
    {
        if  && s.attestation_duties_queue != [] 
            && (
                || s.attestation_duties_queue[0].slot in s.future_att_consensus_instances_already_decided
                || !s.current_attestation_duty.isPresent()
            )    
        {
            
                if s.attestation_duties_queue[0].slot in s.future_att_consensus_instances_already_decided.Keys 
                {
                    var queue_head := s.attestation_duties_queue[0];
                    var new_attestation_slashing_db := f_update_attestation_slashing_db(s.attestation_slashing_db, s.future_att_consensus_instances_already_decided[queue_head.slot]);
                    var s_mod := s.(
                        attestation_duties_queue := s.attestation_duties_queue[1..],
                        future_att_consensus_instances_already_decided := s.future_att_consensus_instances_already_decided - {queue_head.slot},
                        attestation_slashing_db := new_attestation_slashing_db,
                        attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                            s.attestation_consensus_engine_state,
                            new_attestation_slashing_db
                        )                        
                    );
                    lem_f_check_for_next_queued_duty_constants(s_mod, s');
                }
                else
                {
                    // var new_process := s.(
                    //     attestation_duties_queue := s.attestation_duties_queue[1..]
                    // );         
                    // lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_f_start_next_duty();
                }

        }
    }

    lemma lem_f_att_consensus_decided_constants(
        s: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCState
    )
    requires f_att_consensus_decided.requires(s, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(s, id, decided_attestation_data).state
    ensures s'.bn.attestations_submitted == s.bn.attestations_submitted
    ensures s'.rcvd_attestation_shares == s.rcvd_attestation_shares
    decreases s.attestation_duties_queue   
    {
        
        if  || !s.current_attestation_duty.isPresent()
            || id != s.current_attestation_duty.safe_get().slot 
        {
            return;
        }

        var local_current_attestation_duty := s.current_attestation_duty.safe_get();
        var attestation_slashing_db := f_update_attestation_slashing_db(s.attestation_slashing_db, decided_attestation_data);

        var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
        var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
        var attestation_signature_share := rs_sign_attestation(decided_attestation_data, fork_version, attestation_signing_root, s.rs);
        var attestation_with_signature_share := AttestationShare(
                aggregation_bits := get_aggregation_bits(local_current_attestation_duty.validator_index),
                data := decided_attestation_data, 
                signature := attestation_signature_share
            ); 

        var s := 
            s.(
                current_attestation_duty := None,
                attestation_shares_to_broadcast := s.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                attestation_slashing_db := attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    s.attestation_consensus_engine_state,
                    attestation_slashing_db
                )
            );

        lem_f_check_for_next_queued_duty_constants(s, s');             
    } 

    // Note: Lemma's name should be revisited due to second postcondition
    lemma lem_f_listen_for_new_imported_blocks_constants(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(s, block)
    requires s' == f_listen_for_new_imported_blocks(s, block).state
    ensures s'.bn.attestations_submitted == s.bn.attestations_submitted
    ensures s'.rcvd_attestation_shares.Keys <= s.rcvd_attestation_shares.Keys
    ensures forall k | k in s'.rcvd_attestation_shares.Keys :: s'.rcvd_attestation_shares[k] == s.rcvd_attestation_shares[k]
    ensures f_listen_for_new_imported_blocks(s, block).outputs == getEmptyOuputs()
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(s, block);

        var att_consensus_instances_already_decided := s.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(s, att_consensus_instances_already_decided);

        var s :=
                s.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    s.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := s.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := s.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );                     

        if s.current_attestation_duty.isPresent() && s.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            // Stop(current_attestation_duty.safe_get().slot);
            var decided_attestation_data := att_consensus_instances_already_decided[s.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(s.attestation_slashing_db, decided_attestation_data);
            var s := s.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    s.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );
            assert s' == f_check_for_next_queued_duty(s).state;
            lem_f_check_for_next_queued_duty_constants(s, s');
        }
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
    ensures s'.attestation_duties_queue == s.attestation_duties_queue
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
    ensures s'.attestation_duties_queue == s.attestation_duties_queue
    ensures s'.future_att_consensus_instances_already_decided == s.future_att_consensus_instances_already_decided
    {

    }    

    function recover_bls_signature(
        r: Root,
        signature: BLSSignature
    ): BLSPubkey
    requires exists pubkey :: verify_bls_siganture(r, signature, pubkey)
    {
        var pubkey :| verify_bls_siganture(r, signature, pubkey);
        pubkey
    }

    lemma lem_recover_bls_signature()
    ensures forall r, s1, s2 |
                && recover_bls_signature.requires(r, s1)
                && recover_bls_signature.requires(r, s2)
                && recover_bls_signature(r, s1) == recover_bls_signature(r, s2)
            ::
                s1 == s2
    {
        lem_verify_bls_siganture();
    }
    

    lemma lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,

        s': DVCState,
        dv: DVState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires s' == f_listen_for_attestation_shares(process, attestation_share).state
    requires construct_signed_attestation_signature_assumptions_helper(
        process.construct_signed_attestation_signature,
        process.dv_pubkey,
        dv.all_nodes
    )
    requires inv_quorum_constraints(dv)
    requires attestation_share in dv.att_network.allMessagesSent
    requires pred_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(dv, process)
    requires forall a | a in process.bn.attestations_submitted :: exists hn', att_share: AttestationShare ::
    concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(dv, hn', att_share, a)

    ensures forall a | a in s'.bn.attestations_submitted :: exists hn', att_share: AttestationShare :: concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(dv, hn', att_share, a)
    // ensures s'.bn.attestations_submitted == s.bn.attestations_submitted     
    {
        var activate_att_consensus_intances := process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

        if 
            || (activate_att_consensus_intances == {} && !process.latest_attestation_duty.isPresent())
            || (activate_att_consensus_intances != {} && minInSet(activate_att_consensus_intances) <= attestation_share.data.slot)
            || (activate_att_consensus_intances == {} && process.current_attestation_duty.isPresent() && process.current_attestation_duty.safe_get().slot <= attestation_share.data.slot)                
            || (activate_att_consensus_intances == {} && !process.current_attestation_duty.isPresent() && process.latest_attestation_duty.isPresent() && process.latest_attestation_duty.safe_get().slot < attestation_share.data.slot)
            {
                var k := (attestation_share.data, attestation_share.aggregation_bits);
                var attestation_shares_db_at_slot := getOrDefault(process.rcvd_attestation_shares, attestation_share.data.slot, map[]);
                
                var new_attestation_shares_db := 
                        process.rcvd_attestation_shares[
                            attestation_share.data.slot := 
                                attestation_shares_db_at_slot[
                                            k := 
                                                getOrDefault(attestation_shares_db_at_slot, k, {}) + 
                                                {attestation_share}
                                            ]
                                ];

                var process := process.(
                    rcvd_attestation_shares := new_attestation_shares_db
                );

                            
                if process.construct_signed_attestation_signature(process.rcvd_attestation_shares[attestation_share.data.slot][k]).isPresent()
                {
                    var aggregated_attestation := 
                            Attestation(
                                aggregation_bits := attestation_share.aggregation_bits,
                                data := attestation_share.data,
                                signature := process.construct_signed_attestation_signature(process.rcvd_attestation_shares[attestation_share.data.slot][k]).safe_get()
                            );

                    var att_shares := process.rcvd_attestation_shares[attestation_share.data.slot][k];
                    assert construct_signed_attestation_signature_assumptions_helper_reverse(
                        process.construct_signed_attestation_signature,
                        process.dv_pubkey,
                        dv.all_nodes                    
                    );

                    assert process.construct_signed_attestation_signature(att_shares).isPresent();

                    assert construct_signed_attestation_signature_assumptions_helper_reverse(
                        process.construct_signed_attestation_signature,
                        process.dv_pubkey,
                        dv.all_nodes
                    );

                    var data: AttestationData :|
                        construct_signed_attestation_signature_assumptions_helper_reverse_helper(
                            process.construct_signed_attestation_signature,
                            process.dv_pubkey,
                            dv.all_nodes,
                            att_shares,
                            data                
                        );

                    assert pred_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(dv, process);
                    assert att_shares <= dv.att_network.allMessagesSent;

                    var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(data.target.epoch));
                    var signing_root := compute_attestation_signing_root(data, fork_version);
 

                    var signers := 
                    set signer, att_share | 
                        && att_share in att_shares
                        && signer in dv.all_nodes
                        && verify_bls_siganture(signing_root, att_share.signature, signer)
                    ::
                        signer;

                    assert signers <= dv.all_nodes;

                    lemmaThereExistsAnHonestInQuorum(dv.all_nodes, dv.all_nodes - dv.honest_nodes_states.Keys, signers);

                    var h_s :| h_s in dv.honest_nodes_states.Keys && h_s in signers;
                    var h_s_att :| h_s_att in att_shares && verify_bls_siganture(signing_root, h_s_att.signature, h_s);

                    // var attestation_signing_root := compute_attestation_signing_root(data, fork_version);

                    // assert signing_root == attestation_signing_root;                    

                    assert 
                    && h_s in dv.honest_nodes_states.Keys
                    && h_s_att in dv.att_network.allMessagesSent
                    && h_s_att.data == data
                    && verify_bls_siganture(signing_root, h_s_att.signature, h_s);

                    assert 
                    && h_s in dv.honest_nodes_states.Keys
                    && h_s_att in dv.att_network.allMessagesSent
                    && h_s_att.data == data
                    // && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(data.target.epoch));
                    && verify_bls_siganture(signing_root, h_s_att.signature, h_s);

                    // assert pred_attestations_signature_by_honest_node_implies_existence_of_attestation_with_correct_data_helper(
                    //     dv,
                    //     h_s_att,
                    //     h_s,
                    //     signing_root
                    // );

                    // var att_share' :| pred_attestations_signature_by_honest_node_implies_existence_of_attestation_with_correct_data_helper_helper(dv, att_share', signing_root, h_s_att.signature);

                    

                    // assert verify_bls_siganture(attestation_signing_root, h_s_att.signature, h_s);

                    assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(
                        dv,
                        h_s,
                        h_s_att,
                        aggregated_attestation
                    );

                               
                    
                    var    state := process.(
                            bn := process.bn.(
                                attestations_submitted := process.bn.attestations_submitted + [aggregated_attestation]
                            )
                        );

                    forall a | a in state.bn.attestations_submitted 
                    {
                        assert exists hn', att_share: AttestationShare :: concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(dv, hn', att_share, a);
                    }
                    assert s' == state;
                }
            }   
    }

    lemma lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_ex_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,

        s': DVCState,
        dv: DVState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires s' == f_listen_for_attestation_shares(process, attestation_share).state
    requires construct_signed_attestation_signature_assumptions_helper(
        process.construct_signed_attestation_signature,
        process.dv_pubkey,
        dv.all_nodes
    )
    requires inv_quorum_constraints(dv)
    requires attestation_share in dv.att_network.allMessagesSent
    requires pred_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(dv, process)
    // requires forall a | a in process.bn.attestations_submitted :: exists hn', att_share: AttestationShare ::
    // concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(dv, hn', att_share, a)

    // ensures forall a | a in s'.bn.attestations_submitted :: exists hn', att_share: AttestationShare :: concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(dv, hn', att_share, a)
    // ensures s'.bn.attestations_submitted == s.bn.attestations_submitted     

    ensures forall a | a in f_listen_for_attestation_shares(process, attestation_share).outputs.attestations_submitted ::
                        exists hn', att_share: AttestationShare :: concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(dv, hn', att_share, a);
    {
        var activate_att_consensus_intances := process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

        if 
            || (activate_att_consensus_intances == {} && !process.latest_attestation_duty.isPresent())
            || (activate_att_consensus_intances != {} && minInSet(activate_att_consensus_intances) <= attestation_share.data.slot)
            || (activate_att_consensus_intances == {} && process.current_attestation_duty.isPresent() && process.current_attestation_duty.safe_get().slot <= attestation_share.data.slot)                
            || (activate_att_consensus_intances == {} && !process.current_attestation_duty.isPresent() && process.latest_attestation_duty.isPresent() && process.latest_attestation_duty.safe_get().slot < attestation_share.data.slot)
            {
                var k := (attestation_share.data, attestation_share.aggregation_bits);
                var attestation_shares_db_at_slot := getOrDefault(process.rcvd_attestation_shares, attestation_share.data.slot, map[]);
                
                var new_attestation_shares_db := 
                        process.rcvd_attestation_shares[
                            attestation_share.data.slot := 
                                attestation_shares_db_at_slot[
                                            k := 
                                                getOrDefault(attestation_shares_db_at_slot, k, {}) + 
                                                {attestation_share}
                                            ]
                                ];

                var process := process.(
                    rcvd_attestation_shares := new_attestation_shares_db
                );

                            
                if process.construct_signed_attestation_signature(process.rcvd_attestation_shares[attestation_share.data.slot][k]).isPresent()
                {
                    var aggregated_attestation := 
                            Attestation(
                                aggregation_bits := attestation_share.aggregation_bits,
                                data := attestation_share.data,
                                signature := process.construct_signed_attestation_signature(process.rcvd_attestation_shares[attestation_share.data.slot][k]).safe_get()
                            );

                    var att_shares := process.rcvd_attestation_shares[attestation_share.data.slot][k];
                    assert construct_signed_attestation_signature_assumptions_helper_reverse(
                        process.construct_signed_attestation_signature,
                        process.dv_pubkey,
                        dv.all_nodes                    
                    );

                    assert process.construct_signed_attestation_signature(att_shares).isPresent();

                    assert construct_signed_attestation_signature_assumptions_helper_reverse(
                        process.construct_signed_attestation_signature,
                        process.dv_pubkey,
                        dv.all_nodes
                    );

                    var data: AttestationData :|
                        construct_signed_attestation_signature_assumptions_helper_reverse_helper(
                            process.construct_signed_attestation_signature,
                            process.dv_pubkey,
                            dv.all_nodes,
                            att_shares,
                            data                
                        );

                    // assert pred_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(dv, process);
                    // assert att_shares <= dv.att_network.allMessagesSent;

                    var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(data.target.epoch));
                    var signing_root := compute_attestation_signing_root(data, fork_version);
 

                    var signers := 
                    set signer, att_share | 
                        && att_share in att_shares
                        && signer in dv.all_nodes
                        && verify_bls_siganture(signing_root, att_share.signature, signer)
                    ::
                        signer;

                    assert signers <= dv.all_nodes;

                    lemmaThereExistsAnHonestInQuorum(dv.all_nodes, dv.all_nodes - dv.honest_nodes_states.Keys, signers);

                    var h_s :| h_s in dv.honest_nodes_states.Keys && h_s in signers;
                    var h_s_att :| h_s_att in att_shares && verify_bls_siganture(signing_root, h_s_att.signature, h_s);

                    // var attestation_signing_root := compute_attestation_signing_root(data, fork_version);

                    // assert signing_root == attestation_signing_root;                    

                    assert 
                    && h_s in dv.honest_nodes_states.Keys
                    && h_s_att in dv.att_network.allMessagesSent
                    && h_s_att.data == data
                    && verify_bls_siganture(signing_root, h_s_att.signature, h_s);

                    assert 
                    && h_s in dv.honest_nodes_states.Keys
                    && h_s_att in dv.att_network.allMessagesSent
                    && h_s_att.data == data
                    // && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(data.target.epoch));
                    && verify_bls_siganture(signing_root, h_s_att.signature, h_s);

                    // assert pred_attestations_signature_by_honest_node_implies_existence_of_attestation_with_correct_data_helper(
                    //     dv,
                    //     h_s_att,
                    //     h_s,
                    //     signing_root
                    // );

                    // var att_share' :| pred_attestations_signature_by_honest_node_implies_existence_of_attestation_with_correct_data_helper_helper(dv, att_share', signing_root, h_s_att.signature);

                    

                    // assert verify_bls_siganture(attestation_signing_root, h_s_att.signature, h_s);

                    assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(
                        dv,
                        h_s,
                        h_s_att,
                        aggregated_attestation
                    );

                    assert f_listen_for_attestation_shares(process, attestation_share).outputs.attestations_submitted == {aggregated_attestation};

                    assert forall a | a in f_listen_for_attestation_shares(process, attestation_share).outputs.attestations_submitted ::
                        exists hn', att_share: AttestationShare :: concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(dv, hn', att_share, a);
 

                               
                    
                    // var    state := process.(
                    //         bn := process.bn.(
                    //             attestations_submitted := process.bn.attestations_submitted + [aggregated_attestation]
                    //         )
                    //     );

                    // forall a | a in state.bn.attestations_submitted 
                    // {
                    //     assert exists hn', att_share: AttestationShare :: concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(dv, hn', att_share, a);
                    // }
                    // assert s' == state;
                }
            }   
    }    


    lemma lem_pred_rcvd_attestation_shares_is_in_all_messages_sent_f_listen_for_attestation_shares(
        process: DVCState,
        attestation_share: AttestationShare,

        s': DVCState,
        dv: DVState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires s' == f_listen_for_attestation_shares(process, attestation_share).state
    requires pred_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(dv, process)
    requires attestation_share in dv.att_network.allMessagesSent
    ensures pred_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(dv, s') 
    {
        var activate_att_consensus_intances := process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

        if 
            || (activate_att_consensus_intances == {} && !process.latest_attestation_duty.isPresent())
            || (activate_att_consensus_intances != {} && minInSet(activate_att_consensus_intances) <= attestation_share.data.slot)
            || (activate_att_consensus_intances == {} && process.current_attestation_duty.isPresent() && process.current_attestation_duty.safe_get().slot <= attestation_share.data.slot)                
            || (activate_att_consensus_intances == {} && !process.current_attestation_duty.isPresent() && process.latest_attestation_duty.isPresent() && process.latest_attestation_duty.safe_get().slot < attestation_share.data.slot)
            {
                var k := (attestation_share.data, attestation_share.aggregation_bits);
                var attestation_shares_db_at_slot := getOrDefault(process.rcvd_attestation_shares, attestation_share.data.slot, map[]);
                
                var new_attestation_shares_db := 
                        process.rcvd_attestation_shares[
                            attestation_share.data.slot := 
                                attestation_shares_db_at_slot[
                                            k := 
                                                getOrDefault(attestation_shares_db_at_slot, k, {}) + 
                                                {attestation_share}
                                            ]
                                ];

                var process := process.(
                    rcvd_attestation_shares := new_attestation_shares_db
                );

                            
                if process.construct_signed_attestation_signature(process.rcvd_attestation_shares[attestation_share.data.slot][k]).isPresent()
                {
                    var aggregated_attestation := 
                            Attestation(
                                aggregation_bits := attestation_share.aggregation_bits,
                                data := attestation_share.data,
                                signature := process.construct_signed_attestation_signature(process.rcvd_attestation_shares[attestation_share.data.slot][k]).safe_get()
                            );
                               
                    
                    var    state := process.(
                            bn := process.bn.(
                                attestations_submitted := process.bn.attestations_submitted + [aggregated_attestation]
                            )
                        );

                    assert pred_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(dv, s');

                    assert s' == state;
                }
            }   
    }    

    lemma lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_ex_helper(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s)
    // requires event.HonestNodeTakingStep?
    // requires s'.all_nodes == s.all_nodes;
    // requires s'.honest_nodes_states.Keys == s.honest_nodes_states.Keys;
    // requires forall n | n in s'.honest_nodes_states.Keys :: s.honest_nodes_states[n].bn.attestations_submitted == s'.honest_nodes_states[n].bn.attestations_submitted;
    requires s'.all_attestations_created == s.all_attestations_created
    // requires s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;    
    ensures concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');
    {
            // assert s.all
            forall a |
                && a in s'.all_attestations_created
                && is_valid_attestation(a, s'.dv_pubkey)
            ensures exists hn', att_share: AttestationShare :: concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s', hn', att_share, a);
            {
                var hn', att_share: AttestationShare :|
                    concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s, hn', att_share, a);
                
                assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s', hn', att_share, a);
                assert exists hn', att_share: AttestationShare :: concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s', hn', att_share, a);
            }
            // assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');
    }    

    // 1m 10s
    lemma lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s)
    requires construct_signed_attestation_signature_assumptions_helper(
        s.construct_signed_attestation_signature,
        s.dv_pubkey,
        s.all_nodes
    )
    requires inv_only_dv_construct_signed_attestation_signature(s)  
    requires invNetwork(s)
    requires inv_quorum_constraints(s)
    requires pred_rcvd_attestation_shares_is_in_all_messages_sent(s)    
    ensures concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s')
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
                        // // // // Proved
                        // // forall n | n in s'.honest_nodes_states.Keys
                        // // ensures s.honest_nodes_states[n].bn.attestations_submitted == s'.honest_nodes_states[n].bn.attestations_submitted;
                        // // {
                        // //     if n != node 
                        // //     {
                        // //         assert s.honest_nodes_states[n].bn.attestations_submitted == s'.honest_nodes_states[n].bn.attestations_submitted;
                        // //     }
                        // //     else 
                        // //     {
                                lem_f_serve_attestation_duty_constants(s.honest_nodes_states[node], attestation_duty, s'.honest_nodes_states[node]);
                        // //     }
                        // // }
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_ex_helper(s, event, s');
                        assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');  

                    case AttConsensusDecided(id, decided_attestation_data) => 
                        // // Proved
                        lem_f_att_consensus_decided_constants(s.honest_nodes_states[node], id, decided_attestation_data, s'.honest_nodes_states[node]);
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_ex_helper(s, event, s');
                        assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');            

                    case ReceivedAttestationShare(attestation_share) => 
                        assert multiset(addReceipientToMessages<AttestationShare>({attestation_share}, node)) <= s.att_network.messagesInTransit;

                        assert MessaageWithRecipient(message := attestation_share, receipient := node) in s.att_network.messagesInTransit;      

                        var stateAndOutput := f_listen_for_attestation_shares(s_node, attestation_share);  

                        
                        assert attestation_share in s.att_network.allMessagesSent;
                        assert s'.all_attestations_created == s.all_attestations_created + stateAndOutput.outputs.attestations_submitted;

                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_ex_f_listen_for_attestation_shares(
                            s_node,
                            attestation_share,
                            s'_node,
                            s
                        );

                        forall a | 
                                    && a in s'.all_attestations_created
                                    && is_valid_attestation(a, s'.dv_pubkey)
                        ensures exists hn', att_share: AttestationShare :: concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s', hn', att_share, a);            
                        {
                            if a in s.all_attestations_created
                            {
                                var hn', att_share: AttestationShare :| concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s, hn', att_share, a);
                                assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s', hn', att_share, a);
                            }
                            else 
                            {
                                assert a in stateAndOutput.outputs.attestations_submitted;
                                var hn', att_share: AttestationShare :| concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s, hn', att_share, a);
                                assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s', hn', att_share, a);
                            }                                   
                        }                                

                        assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');         

                    case ImportedNewBlock(block) => 
                        // // Provded
                        var s_node := add_block_to_bn(s_node, nodeEvent.block);
                        lem_f_listen_for_new_imported_blocks_constants(s_node, block, s'_node);
                        assert s'.all_attestations_created == s.all_attestations_created;
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_ex_helper(s, event, s');
                        assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');     

                    case ResendAttestationShares => 
                        // // Proved
                        assert s'.all_attestations_created == s.all_attestations_created;
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_ex_helper(s, event, s');
                        assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');

                    case NoEvent => 
                        // // Proved
                        assert s'.all_attestations_created == s.all_attestations_created;
                        lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_ex_helper(s, event, s');
                        assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                // lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_helper(s, event, s');
                // assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');
                forall a | 
                    && a in s'.all_attestations_created
                    && is_valid_attestation(a, s'.dv_pubkey)
                ensures exists hn', att_share: AttestationShare :: concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s', hn', att_share, a);      
                {
                    if a in s.all_attestations_created
                    {
                        var hn', att_share: AttestationShare :| concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s, hn', att_share, a);
                        assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(s', hn', att_share, a);                        
                    }
                    else 
                    {
                        var attestation_shares :| 
                            && attestation_shares <= s'.att_network.allMessagesSent
                            // && var sig_shares := set x | x in attestation_shares :: x.signature;
                            && var constructed_sig := s.construct_signed_attestation_signature(attestation_shares);
                            && constructed_sig.isPresent()
                            && constructed_sig.safe_get() == a.signature
                            ;      

                        var constructed_sig := s.construct_signed_attestation_signature(attestation_shares);         

                        var data: AttestationData :|
                            construct_signed_attestation_signature_assumptions_helper_reverse_helper(
                                s.construct_signed_attestation_signature,
                                s.dv_pubkey,
                                s.all_nodes,
                                attestation_shares,
                                data                
                            );   

                        var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(data.target.epoch));
                        var signing_root := compute_attestation_signing_root(data, fork_version);
    

                        var signers := 
                        set signer, att_share | 
                            && att_share in attestation_shares
                            && signer in s.all_nodes
                            && verify_bls_siganture(signing_root, att_share.signature, signer)
                        ::
                            signer;            

                        assert signers <= s.all_nodes;

                        lemmaThereExistsAnHonestInQuorum(s.all_nodes, s.all_nodes - s.honest_nodes_states.Keys, signers);  

                        var h_s :| h_s in s.honest_nodes_states.Keys && h_s in signers;
                        var h_s_att :| h_s_att in attestation_shares && verify_bls_siganture(signing_root, h_s_att.signature, h_s);     

                        assert 
                        && h_s in s.honest_nodes_states.Keys
                        && h_s_att in s.att_network.allMessagesSent
                        && h_s_att.data == data
                        && verify_bls_siganture(signing_root, h_s_att.signature, h_s);

                        assert 
                        && h_s in s.honest_nodes_states.Keys
                        && h_s_att in s.att_network.allMessagesSent
                        && h_s_att.data == data
                        // && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(data.target.epoch));
                        && verify_bls_siganture(signing_root, h_s_att.signature, h_s);    

                        compute_signing_root_properties<AttestationData>();
                        lem_verify_bls_siganture();

                        var a_fork_version := bn_get_fork_version(compute_start_slot_at_epoch(a.data.target.epoch));
                        var a_attestation_signing_root := compute_attestation_signing_root(a.data, a_fork_version);       

                        assert verify_bls_siganture(signing_root, a.signature, s'.dv_pubkey);

                        assert verify_bls_siganture(a_attestation_signing_root, a.signature, s'.dv_pubkey);             

                        // assert 

                        assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(
                            s,
                            h_s,
                            h_s_att,
                            a
                        );      

                        assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(
                            s',
                            h_s,
                            h_s_att,
                            a
                        );                                                                                                                                                 
                    }
                }
                assert concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s');
        }
    }        

    lemma lem_pred_rcvd_attestation_shares_is_in_all_messages_sent(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires invNetwork(s)
    requires pred_rcvd_attestation_shares_is_in_all_messages_sent(s)
    ensures pred_rcvd_attestation_shares_is_in_all_messages_sent(s')
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        lem_f_serve_attestation_duty_constants(s_node, attestation_duty, s'_node);
                        assert pred_rcvd_attestation_shares_is_in_all_messages_sent(s');                    
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lem_f_att_consensus_decided_constants(s_node, id, decided_attestation_data, s'_node);
                        assert pred_rcvd_attestation_shares_is_in_all_messages_sent(s');                    
                    case ReceivedAttestationShare(attestation_share) => 
                        assert multiset(addReceipientToMessages<AttestationShare>({attestation_share}, node)) <= s.att_network.messagesInTransit;

                        assert MessaageWithRecipient(message := attestation_share, receipient := node) in s.att_network.messagesInTransit;        

                        
                        assert attestation_share in s.att_network.allMessagesSent;                    
                        lem_pred_rcvd_attestation_shares_is_in_all_messages_sent_f_listen_for_attestation_shares(
                            s_node,
                            attestation_share,
                            s'_node,
                            s
                        );
                        assert pred_rcvd_attestation_shares_is_in_all_messages_sent(s');
                    case ImportedNewBlock(block) => 
                        var s_node := add_block_to_bn(s_node, nodeEvent.block);
                        lem_f_listen_for_new_imported_blocks_constants(s_node, block, s'_node);
                        assert pred_rcvd_attestation_shares_is_in_all_messages_sent(s');                    
                    case ResendAttestationShares => 
                        assert pred_rcvd_attestation_shares_is_in_all_messages_sent(s');                    
                    case NoEvent => 
                        assert pred_rcvd_attestation_shares_is_in_all_messages_sent(s');
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                assert pred_rcvd_attestation_shares_is_in_all_messages_sent(s');
        }
    }     

    lemma lem_pred_data_of_att_share_is_decided_value_helper(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires pred_data_of_att_share_is_decided_value(s)
    requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    requires inv_quorum_constraints(s)
    requires inv_queued_att_duty_is_rcvd_duty3(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires |s.all_nodes| > 0
    requires s'.att_network.allMessagesSent == s.att_network.allMessagesSent + 
                            getMessagesFromMessagesWithRecipient({});
    ensures  pred_data_of_att_share_is_decided_value(s');
    {
        forall cid | cid in s.consensus_on_attestation_data.Keys 
        ensures 
            var s_consensus := s.consensus_on_attestation_data[cid];
            var s'_consensus := s'.consensus_on_attestation_data[cid];
            s_consensus.decided_value.isPresent() ==> 
                && s'_consensus.decided_value.isPresent()
                && s_consensus.decided_value.safe_get() == s'_consensus.decided_value.safe_get()
            ;
        {
            var s_consensus := s.consensus_on_attestation_data[cid];
            var s'_consensus := s'.consensus_on_attestation_data[cid];

            assert isConditionForSafetyTrue(s_consensus);
            assert s_consensus.decided_value.isPresent() ==> 
                && s'_consensus.decided_value.isPresent()
                && s_consensus.decided_value.safe_get() == s'_consensus.decided_value.safe_get()
            ;
        }
        assert pred_data_of_att_share_is_decided_value(s');        
    }     

    lemma lem_consensus_next_under_safety<D(!new, 0)>(
        s: ConsensusInstance,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,        
        s': ConsensusInstance,
        output: Optional<OutCommand>
    )
    requires ConsensusSpec.Next(s, honest_nodes_validity_predicates, s', output)
    requires isConditionForSafetyTrue(s)
    requires s.decided_value.isPresent()
    ensures s'.decided_value.isPresent()
    ensures s.decided_value.safe_get() == s'.decided_value.safe_get()
    {

    }

    // TODO: Rewarite the following three lemmas. Not sure how yet. But I think that they should be rewritten in a more "modular" way
    lemma lem_pred_data_of_att_share_is_decided_value_att_consensus_decided_helper_1(
        s: DVState,
        event: DV.Event,
        s': DVState,
        hn: BLSPubkey,
        att_share: AttestationShare
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event.event.AttConsensusDecided?
    requires pred_data_of_att_share_is_decided_value(s)
    requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)  
    requires inv_quorum_constraints(s)
    requires inv_unchanged_honesty(s)
    requires inv_queued_att_duty_is_rcvd_duty3(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc(s)          
    requires |s.all_nodes| > 0    
    requires
                && hn in s'.honest_nodes_states.Keys 
                && att_share in s'.att_network.allMessagesSent
                && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));
                && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
                && verify_bls_siganture(attestation_signing_root, att_share.signature, hn)   
    requires att_share in s.att_network.allMessagesSent
    ensures
                && s'.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent()                                     
                && s'.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case AttConsensusDecided(id: Slot, decided_attestation_data) => 

                        assert s.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent();
                        assert s.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;   

                        var s_w_honest_node_states_updated := lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_get_s_w_honest_node_states_updated(s, node, nodeEvent);           
                        var cid := att_share.data.slot;

                        assert s_w_honest_node_states_updated.consensus_on_attestation_data == s.consensus_on_attestation_data;


                        var output := 
                            if nodeEvent.AttConsensusDecided? && nodeEvent.id == cid then 
                                Some(Decided(node, nodeEvent.decided_attestation_data))
                            else
                                None
                            ;

                        var validityPredicates := 
                            map n |
                                    && n in s_w_honest_node_states_updated.honest_nodes_states.Keys 
                                    && cid in s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
                                ::
                                    s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances[cid].validityPredicate
                            ;

                        var s_consensus := s_w_honest_node_states_updated.consensus_on_attestation_data[cid];
                        var s'_consensus := s'.consensus_on_attestation_data[cid];                

                        assert
                            ConsensusSpec.Next(
                                s_consensus,
                                validityPredicates,
                                s'_consensus,
                                output
                            );      

                        lem_consensus_next_under_safety(
                            s_consensus,
                            validityPredicates,
                            s'_consensus,
                            output                                
                        );                        
                            
                        assert s'.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent();
                        assert s.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == s'.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get();
                        assert s'.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;                              
                }
        }
    }

    lemma lem_pred_data_of_att_share_is_decided_value_att_consensus_decided_helper_helper(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event.event.AttConsensusDecided?
    requires inv_quorum_constraints(s)
    requires inv_unchanged_honesty(s)        
    requires |s.all_nodes| > 0    
    ensures s'.consensus_on_attestation_data[event.event.id].decided_value.safe_get() == event.event.decided_attestation_data; 
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case AttConsensusDecided(id: Slot, decided_attestation_data) => 

                        var s_w_honest_node_states_updated := lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_get_s_w_honest_node_states_updated(s, node, nodeEvent);           
                        var cid := id;

                        assert s_w_honest_node_states_updated.consensus_on_attestation_data == s.consensus_on_attestation_data;


                        var output := Some(Decided(node, nodeEvent.decided_attestation_data)); 

                        var validityPredicates := 
                            map n |
                                    && n in s_w_honest_node_states_updated.honest_nodes_states.Keys 
                                    && cid in s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
                                ::
                                    s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances[cid].validityPredicate
                            ;

                        var s_consensus := s_w_honest_node_states_updated.consensus_on_attestation_data[cid];
                        var s'_consensus := s'.consensus_on_attestation_data[cid];                

                        assert
                            ConsensusSpec.Next(
                                s_consensus,
                                validityPredicates,
                                s'_consensus,
                                output
                            );                               


                        assert s'.consensus_on_attestation_data[id].decided_value.isPresent();
                        assert isConditionForSafetyTrue(s'_consensus);
                        assert s'_consensus.decided_value.safe_get() == decided_attestation_data; 
                        assert s'.consensus_on_attestation_data[id].decided_value.safe_get() == decided_attestation_data; 
                }
        }            
    }



    lemma lem_pred_data_of_att_share_is_decided_value_att_consensus_decided_helper(
        s: DVState,
        event: DV.Event,
        s': DVState,
        hn: BLSPubkey,
        att_share: AttestationShare
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event.event.AttConsensusDecided?
    requires pred_data_of_att_share_is_decided_value(s)
    requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)  
    requires inv_quorum_constraints(s)
    requires inv_unchanged_honesty(s)
    requires inv_queued_att_duty_is_rcvd_duty3(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc(s)          
    requires |s.all_nodes| > 0    
    requires
                && hn in s'.honest_nodes_states.Keys 
                && att_share in s'.att_network.allMessagesSent
                && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));
                && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
                && verify_bls_siganture(attestation_signing_root, att_share.signature, hn)   
    requires    var s_node := s.honest_nodes_states[event.node];
                && s_node.current_attestation_duty.isPresent()
                && event.event.id == s_node.current_attestation_duty.safe_get().slot
    ensures
                && s'.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent()                                     
                && s'.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case AttConsensusDecided(id: Slot, decided_attestation_data) => 
                        var local_current_attestation_duty := s_node.current_attestation_duty.safe_get();
                        var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
                        var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
                        var attestation_signature_share := rs_sign_attestation(decided_attestation_data, fork_version, attestation_signing_root, s_node.rs);
                        var attestation_with_signature_share := AttestationShare(
                                aggregation_bits := get_aggregation_bits(local_current_attestation_duty.validator_index),
                                data := decided_attestation_data, 
                                signature := attestation_signature_share
                            ); 

                        var messagesToBeSent := f_att_consensus_decided(s_node, id, decided_attestation_data).outputs.att_shares_sent;
                        assert messagesToBeSent ==  multicast(attestation_with_signature_share, s_node.peers);     
                        assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent + 
                            getMessagesFromMessagesWithRecipient(messagesToBeSent); 
                        assert forall m | m in messagesToBeSent :: m.message == attestation_with_signature_share; 
                        lemmaOnGetMessagesFromMessagesWithRecipientWhenAllMessagesAreTheSame(messagesToBeSent, attestation_with_signature_share);    
                        assert getMessagesFromMessagesWithRecipient(messagesToBeSent) ==  {attestation_with_signature_share};
                        assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent + 
                            {attestation_with_signature_share}; 

 

                                                                     

                        if att_share in s.att_network.allMessagesSent
                        {
                            lem_pred_data_of_att_share_is_decided_value_att_consensus_decided_helper_1(s, event, s', hn, att_share);                           
                        }
                        else
                        {
                            assert att_share == attestation_with_signature_share;
                            lemmaImaptotalElementInDomainIsInKeys(s.consensus_on_attestation_data, id);
                            assert id in s.consensus_on_attestation_data.Keys ;
                            lem_pred_data_of_att_share_is_decided_value_att_consensus_decided_helper_helper(s, event, s');

                            assert s'.consensus_on_attestation_data[id].decided_value.safe_get() == decided_attestation_data; 
                            assert s'.consensus_on_attestation_data[id].decided_value.safe_get() == att_share.data; 
                            lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s, event, s');   
                            
                            assert  att_share.data.slot == id;
                            assert s'.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent();                             
                            assert s'.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data; 
                        }  
                }
        }            
    }

    lemma lem_pred_data_of_att_share_is_decided_value_att_consensus_decided(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event.event.AttConsensusDecided?
    requires pred_data_of_att_share_is_decided_value(s)
    requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)  
    requires inv_quorum_constraints(s)
    requires inv_unchanged_honesty(s)
    requires inv_queued_att_duty_is_rcvd_duty3(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc(s)          
    requires |s.all_nodes| > 0
    ensures pred_data_of_att_share_is_decided_value(s')   
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case AttConsensusDecided(id: Slot, decided_attestation_data) => 
                        if  && s_node.current_attestation_duty.isPresent()
                            && id == s_node.current_attestation_duty.safe_get().slot
                        {
                            var local_current_attestation_duty := s_node.current_attestation_duty.safe_get();

                            var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
                            var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
                            var attestation_signature_share := rs_sign_attestation(decided_attestation_data, fork_version, attestation_signing_root, s_node.rs);
                            var attestation_with_signature_share := AttestationShare(
                                    aggregation_bits := get_aggregation_bits(local_current_attestation_duty.validator_index),
                                    data := decided_attestation_data, 
                                    signature := attestation_signature_share
                                ); 

                            var messagesToBeSent := f_att_consensus_decided(s_node, id, decided_attestation_data).outputs.att_shares_sent;
                            assert messagesToBeSent ==  multicast(attestation_with_signature_share, s_node.peers);     
                            assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent + 
                                getMessagesFromMessagesWithRecipient(messagesToBeSent); 
                            assert forall m | m in messagesToBeSent :: m.message == attestation_with_signature_share; 
                            lemmaOnGetMessagesFromMessagesWithRecipientWhenAllMessagesAreTheSame(messagesToBeSent, attestation_with_signature_share);    
                            assert getMessagesFromMessagesWithRecipient(messagesToBeSent) ==  {attestation_with_signature_share};
                            assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent + 
                                {attestation_with_signature_share}; 

                            forall hn, att_share |
                                    && hn in s'.honest_nodes_states.Keys 
                                    && att_share in s'.att_network.allMessagesSent
                                    && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));
                                    && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
                                    && verify_bls_siganture(attestation_signing_root, att_share.signature, hn)
                            ensures s'.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent();
                            ensures s'.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;     
                            {
                                lem_pred_data_of_att_share_is_decided_value_att_consensus_decided_helper(s, event, s', hn, att_share);
                            }                            

                            assert pred_data_of_att_share_is_decided_value(s');
                        }
                        else 
                        {
                            forall hn, att_share |
                                    && hn in s'.honest_nodes_states.Keys 
                                    && att_share in s'.att_network.allMessagesSent
                                    && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));
                                    && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
                                    && verify_bls_siganture(attestation_signing_root, att_share.signature, hn)
                            ensures s'.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent();
                            ensures s'.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;     
                            {
                                assert att_share in s.att_network.allMessagesSent;
                                lem_pred_data_of_att_share_is_decided_value_att_consensus_decided_helper_1(s, event, s', hn, att_share);
                            } 
                            assert pred_data_of_att_share_is_decided_value(s');
                        }

                }
        }
    }

    lemma lem_pred_data_of_att_share_is_decided_value_att_adversary(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.AdeversaryTakingStep?
    requires pred_data_of_att_share_is_decided_value(s)
    requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)  
    requires inv_quorum_constraints(s)
    requires inv_queued_att_duty_is_rcvd_duty3(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires |s.all_nodes| > 0
    ensures pred_data_of_att_share_is_decided_value(s') 
    {
        var new_attestation_shares_sent := s'.att_network.allMessagesSent - s.att_network.allMessagesSent;

        forall hn, att_share |
                && hn in s'.honest_nodes_states.Keys 
                && att_share in s'.att_network.allMessagesSent
                && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));
                && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
                && verify_bls_siganture(attestation_signing_root, att_share.signature, hn)
        ensures s'.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent();
        ensures s'.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;                          
        {
            var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));
            var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);        

            if att_share in s.att_network.allMessagesSent
            {
                assert s.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent();
                assert s.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;   
            }
            else
            {
                forall signer | verify_bls_siganture(attestation_signing_root, att_share.signature, signer)
                ensures signer in s.adversary.nodes;
                ensures signer !in  s.honest_nodes_states.Keys; 
                {

                    assert signer in s.adversary.nodes; 
                    lemmaEmptyIntersectionImpliesDisjointness(s.adversary.nodes, s.honest_nodes_states.Keys);
                    assert s.adversary.nodes !! s.honest_nodes_states.Keys;
                    assert signer !in  s.honest_nodes_states.Keys;
                }              
                assert false;          
            }
        }
    
        assert pred_data_of_att_share_is_decided_value(s');
    }      

    lemma lem_pred_data_of_att_share_is_decided_value_helper2<M>(
        allMessagesSent': set<M>,
        allMessagesSent: set<M>,
        messagesToBeSent: set<MessaageWithRecipient<M>>
    )
    requires allMessagesSent' == allMessagesSent + 
                                getMessagesFromMessagesWithRecipient(messagesToBeSent);
    requires messagesToBeSent == {}
    ensures allMessagesSent' == allMessagesSent
    {

    }

    // Ver time: 1m 35s
    lemma lem_pred_data_of_att_share_is_decided_value(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_quorum_constraints(s)
    requires inv_unchanged_honesty(s)
    requires inv_queued_att_duty_is_rcvd_duty3(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires pred_data_of_att_share_is_decided_value(s)
    requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)      
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist(s)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc(s)          
    requires |s.all_nodes| > 0
    ensures pred_data_of_att_share_is_decided_value(s')   
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                if nodeEvent.AttConsensusDecided? 
                {
                    lem_pred_data_of_att_share_is_decided_value_att_consensus_decided(s, event, s');
                }
                else 
                {
                    match nodeEvent
                    {
                        case ServeAttstationDuty(attestation_duty) => 
                            var messagesToBeSent := f_serve_attestation_duty(s_node, attestation_duty).outputs.att_shares_sent;
                            assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent + 
                                getMessagesFromMessagesWithRecipient(messagesToBeSent);
                            lem_f_serve_attestation_duty_constants(s_node, attestation_duty, s'_node);
                            assert messagesToBeSent == {};
                            lem_pred_data_of_att_share_is_decided_value_helper2(s'.att_network.allMessagesSent, s.att_network.allMessagesSent, messagesToBeSent);
                            assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent;
                            
                                                                    
                        case ReceivedAttestationShare(attestation_share) => 
                            var messagesToBeSent := f_listen_for_attestation_shares(s_node, attestation_share).outputs.att_shares_sent;
                            assert messagesToBeSent == {};                        
                            assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent + 
                                getMessagesFromMessagesWithRecipient(messagesToBeSent);
                            assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent + 
                                getMessagesFromMessagesWithRecipient({});                                              

                        case ImportedNewBlock(block) => 
                            var s_node := add_block_to_bn(s_node, nodeEvent.block);
                            var messagesToBeSent := f_listen_for_new_imported_blocks(s_node, block).outputs.att_shares_sent;
                            assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent + 
                                getMessagesFromMessagesWithRecipient(messagesToBeSent);
                            lem_f_listen_for_new_imported_blocks_constants(s_node, block, s'_node);
                            assert messagesToBeSent == {};
                            lem_pred_data_of_att_share_is_decided_value_helper2(s'.att_network.allMessagesSent, s.att_network.allMessagesSent, messagesToBeSent);
                            assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent;                 
                    
                        case ResendAttestationShares => 
                            var messagesToBeSent := f_resend_attestation_share(s_node).outputs.att_shares_sent;     

                            assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent + 
                                getMessagesFromMessagesWithRecipient(messagesToBeSent);  

                            forall m | m in getMessagesFromMessagesWithRecipient(messagesToBeSent)  
                            ensures m in s.att_network.allMessagesSent
                            {
                                assert m in s_node.attestation_shares_to_broadcast.Values;
                                assert m in s.att_network.allMessagesSent;
                            }        

                            assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent;

                        case NoEvent => 
                            assert s'.att_network == s.att_network;
                    }
                    lem_pred_data_of_att_share_is_decided_value_helper(s, event, s');
                }


            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                lem_pred_data_of_att_share_is_decided_value_att_adversary(s, event, s');

        }        
    }   

    lemma  lemmaNextConsensus<D(!new, 0)>(
        s: ConsensusInstance,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,        
        s': ConsensusInstance,
        output: Optional<OutCommand>
    )
    requires ConsensusSpec.Next(
                        s,
                        honest_nodes_validity_predicates,
                        s',
                        output
                    );
    ensures s.honest_nodes_validity_functions.Keys <= s'.honest_nodes_validity_functions.Keys;                 
    {
    }

    lemma  lemmaNextConsensus2<D(!new, 0)>(
        s: ConsensusInstance,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,        
        s': ConsensusInstance,
        output: Optional<OutCommand>,
        n: BLSPubkey
    )
    requires ConsensusSpec.Next(
                        s,
                        honest_nodes_validity_predicates,
                        s',
                        output
                    );
    requires n in s.honest_nodes_validity_functions.Keys
    ensures s.honest_nodes_validity_functions[n] <= s'.honest_nodes_validity_functions[n];                    
    {
    }    

    // 1m 15s
    lemma lem_inv_decided_value_of_consensus_instance_is_decided_by_quorum_helper(
        s: DVState,
        event: DV.Event,
        cid: Slot,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires cid in s'.consensus_on_attestation_data.Keys
    requires inv_quorum_constraints(s)
    requires inv_queued_att_duty_is_rcvd_duty3(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)    
    requires s.consensus_on_attestation_data[cid].decided_value.isPresent()
    ensures is_a_valid_decided_value(s'.consensus_on_attestation_data[cid]); 
    // ensures inv_decided_value_of_consensus_instance_is_decided_by_quorum(s')   
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];

                var s_w_honest_node_states_updated :=
                    if nodeEvent.ImportedNewBlock? then 
                        s.(
                            honest_nodes_states := s.honest_nodes_states[node := add_block_to_bn(s.honest_nodes_states[node], nodeEvent.block)]
                        )
                    else 
                        s 
                    ;                

                assert s_w_honest_node_states_updated.consensus_on_attestation_data == s.consensus_on_attestation_data;


                var output := 
                    if nodeEvent.AttConsensusDecided? && nodeEvent.id == cid then 
                        Some(Decided(node, nodeEvent.decided_attestation_data))
                    else
                        None
                    ;

                var validityPredicates := 
                    map n |
                            && n in s_w_honest_node_states_updated.honest_nodes_states.Keys 
                            && cid in s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
                        ::
                            s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances[cid].validityPredicate
                    ;

                var s_consensus := s_w_honest_node_states_updated.consensus_on_attestation_data[cid];
                var s'_consensus := s'.consensus_on_attestation_data[cid];                

                assert
                    ConsensusSpec.Next(
                        s_consensus,
                        validityPredicates,
                        s'_consensus,
                        output
                    );



                // assert s_consensus == s'.consensus_on_attestation_data[cid];

                // if s_consensus.decided_value.isPresent()
                {
                    assert isConditionForSafetyTrue(s_consensus);
                    assert 
                        && s'_consensus.decided_value.isPresent()
                        && s_consensus.decided_value.safe_get() == s'_consensus.decided_value.safe_get()
                    ;

                    var h_nodes :| is_a_valid_decided_value_according_to_set_of_nodes(s_consensus, h_nodes); 

                    assert s_consensus.honest_nodes_validity_functions.Keys <= s'_consensus.honest_nodes_validity_functions.Keys;
                    assert         
                        && var byz := s'.all_nodes - s'_consensus.honest_nodes_status.Keys;
                        |h_nodes| >= quorum(|s.all_nodes|) - |byz|;

                    lemmaNextConsensus(
                        s_consensus,
                        validityPredicates,
                        s'_consensus,
                        output                        
                    );


                    forall n | n in h_nodes 
                    ensures exists vp: AttestationData -> bool :: vp in s'_consensus.honest_nodes_validity_functions[n] && vp(s'_consensus.decided_value.safe_get());
                    {
                        assert is_a_valid_decided_value(s_consensus); 
                        var vp: AttestationData -> bool :| vp in s_consensus.honest_nodes_validity_functions[n] && vp(s_consensus.decided_value.safe_get()); 
                        lemmaNextConsensus2(
                            s_consensus,
                            validityPredicates,
                            s'_consensus,
                            output,
                            n                       
                        );                        
                        assert vp in  s'_consensus.honest_nodes_validity_functions[n]; 
                        assert vp(s'_consensus.decided_value.safe_get());
                        assert exists vp: AttestationData -> bool :: vp in s'_consensus.honest_nodes_validity_functions[n] && vp(s'_consensus.decided_value.safe_get());
                    }

                            

                    assert is_a_valid_decided_value_according_to_set_of_nodes(s'_consensus, h_nodes); 
                    assert is_a_valid_decided_value(s'_consensus); 
                }
                // else
                // {
                //     assert is_a_valid_decided_value(s'_consensus); 
                // }

        }
    }   

    lemma lem_inv_decided_value_of_consensus_instance_is_decided_by_quorum(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_quorum_constraints(s)
    requires inv_queued_att_duty_is_rcvd_duty3(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)    
    ensures inv_decided_value_of_consensus_instance_is_decided_by_quorum(s')   
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];

                var s_w_honest_node_states_updated :=
                    if nodeEvent.ImportedNewBlock? then 
                        s.(
                            honest_nodes_states := s.honest_nodes_states[node := add_block_to_bn(s.honest_nodes_states[node], nodeEvent.block)]
                        )
                    else 
                        s 
                    ;                

                forall cid | 
                        && cid in s'.consensus_on_attestation_data.Keys
                        && s'.consensus_on_attestation_data[cid].decided_value.isPresent()
                ensures is_a_valid_decided_value(s'.consensus_on_attestation_data[cid]);
                {
                    if s.consensus_on_attestation_data[cid].decided_value.isPresent()
                    {
                        lem_inv_decided_value_of_consensus_instance_is_decided_by_quorum_helper(s, event, cid, s');
                    }
                    else
                    {
                        assert is_a_valid_decided_value(s'.consensus_on_attestation_data[cid]);
                    }
                }
                assert inv_decided_value_of_consensus_instance_is_decided_by_quorum(s');
               

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                assert inv_decided_value_of_consensus_instance_is_decided_by_quorum(s');
        }        
    } 

    lemma lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k_helper(
        s: DVState,
        cid: Slot
    )
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist(s)
    requires inv_quorum_constraints(s)
    requires inv_unchanged_honesty(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires cid in s.consensus_on_attestation_data.Keys
    requires s.consensus_on_attestation_data[cid].decided_value.isPresent()
    ensures s.consensus_on_attestation_data[cid].decided_value.safe_get().slot == cid
    {
        var s_consensus := s.consensus_on_attestation_data[cid];
        assert is_a_valid_decided_value(s_consensus);  

        var h_nodes_a :| is_a_valid_decided_value_according_to_set_of_nodes(s_consensus, h_nodes_a);

        var byz := s.all_nodes - s.honest_nodes_states.Keys;

        assert byz * h_nodes_a == {} by 
        {
            assert s.honest_nodes_states.Keys * byz == {};
        }

        lemmaThereExistsAnHonestInQuorum2(s.all_nodes, byz, h_nodes_a);  

        var h_n :| h_n in h_nodes_a;  

        var vp: AttestationData -> bool :| vp in s_consensus.honest_nodes_validity_functions[h_n] && vp(s_consensus.decided_value.safe_get());  

        var attestation_duty, attestation_slashing_db :|
                inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_body(cid, attestation_duty, attestation_slashing_db, vp);

        assert s_consensus.decided_value.safe_get().slot == cid;
    }

    lemma lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc(s)  
    requires inv_quorum_constraints(s)
    requires inv_unchanged_honesty(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)  
    ensures inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s') 
    {
        lem_inv_quorum_constraints_dv_next(s, event, s');
        lem_inv_unchanged_honesty_dv_next(s, event, s');
        lem_inv_only_dv_construct_signed_attestation_signature_dv_next(s, event, s');
        lem_inv_decided_value_of_consensus_instance_is_decided_by_quorum(s, event, s');
        lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist(s, event, s');
        lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k2(s');   
    }     

    lemma lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k2(
        s: DVState
    )
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist(s)
    requires inv_quorum_constraints(s)
    requires inv_unchanged_honesty(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    ensures inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s) 
    {
        forall cid |
            && cid in s.consensus_on_attestation_data.Keys
            && s.consensus_on_attestation_data[cid].decided_value.isPresent()
        {
           lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k_helper(s, cid);
        }        
    }        

     

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_get_s_w_honest_node_states_updated(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Types.Event
    ) returns (s_w_honest_node_states_updated: DVState)
    requires node in s.honest_nodes_states
    ensures s_w_honest_node_states_updated == add_block_to_bn_with_event(s, node, nodeEvent)
    ensures s_w_honest_node_states_updated == s.(honest_nodes_states := s_w_honest_node_states_updated.honest_nodes_states)
    ensures s_w_honest_node_states_updated.honest_nodes_states == s.honest_nodes_states[node := s_w_honest_node_states_updated.honest_nodes_states[node]]
    ensures s_w_honest_node_states_updated.honest_nodes_states[node] == s.honest_nodes_states[node].(bn := s_w_honest_node_states_updated.honest_nodes_states[node].bn)
    {
        s_w_honest_node_states_updated :=
            if nodeEvent.ImportedNewBlock? then 
                s.(
                    honest_nodes_states := s.honest_nodes_states[node := add_block_to_bn(s.honest_nodes_states[node], nodeEvent.block)]
                )
            else 
                s 
            ;         
    }

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_get_s_w_honest_node_states_updated_2(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Types.Event,
        node': BLSPubkey,
        s_w_honest_node_states_updated: DVState
    ) 
    requires node in s.honest_nodes_states
    requires node' in s.honest_nodes_states
    requires s_w_honest_node_states_updated == add_block_to_bn_with_event(s, node, nodeEvent)
    ensures s_w_honest_node_states_updated.honest_nodes_states[node'].attestation_consensus_engine_state == s.honest_nodes_states[node'].attestation_consensus_engine_state
    {      
    }    

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_helper(
        s: DVState,
        event: DV.Event,
        s': DVState,
        cid: Slot,
        hn: BLSPubkey,
        vp: AttestationData -> bool
    )   returns (attestation_duty: AttestationDuty, attestation_slashing_db: set<SlashingDBAttestation>)
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')    
    requires inv_quorum_constraints(s)
    requires inv_unchanged_honesty(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)      
    requires
            && hn in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions.Keys
            && vp in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions[hn]
    requires event.HonestNodeTakingStep?
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc(s)
    ensures inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_body(cid, attestation_duty, attestation_slashing_db, vp); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];

                var s_w_honest_node_states_updated :=
                    lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_get_s_w_honest_node_states_updated(s, node, nodeEvent);         

                assert s_w_honest_node_states_updated.consensus_on_attestation_data == s.consensus_on_attestation_data;


                var output := 
                    if nodeEvent.AttConsensusDecided? && nodeEvent.id == cid then 
                        Some(Decided(node, nodeEvent.decided_attestation_data))
                    else
                        None
                    ;

                var validityPredicates := 
                    map n |
                            && n in s_w_honest_node_states_updated.honest_nodes_states.Keys 
                            && cid in s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
                        ::
                            s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances[cid].validityPredicate
                    ;

                var s_consensus := s_w_honest_node_states_updated.consensus_on_attestation_data[cid];
                var s'_consensus := s'.consensus_on_attestation_data[cid];                

                assert
                    ConsensusSpec.Next(
                        s_consensus,
                        validityPredicates,
                        s'_consensus,
                        output
                    );

            if hn in s_consensus.honest_nodes_validity_functions.Keys  && vp in s_consensus.honest_nodes_validity_functions[hn]
            {
                assert vp in s'_consensus.honest_nodes_validity_functions[hn];

                attestation_duty, attestation_slashing_db :| inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_body(cid, attestation_duty, attestation_slashing_db, vp);

            }
            else 
            {
                assert vp in validityPredicates.Values;
                var vpn :| vpn in validityPredicates.Keys && validityPredicates[vpn] == vp;
                assert validityPredicates[vpn] == s_w_honest_node_states_updated.honest_nodes_states[vpn].attestation_consensus_engine_state.active_attestation_consensus_instances[cid].validityPredicate;

                assert vpn in s.honest_nodes_states.Keys;
                assert cid in s_w_honest_node_states_updated.honest_nodes_states[vpn].attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

                lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_get_s_w_honest_node_states_updated_2(s, node, nodeEvent, vpn, s_w_honest_node_states_updated);

                assert s_w_honest_node_states_updated.honest_nodes_states[vpn].attestation_consensus_engine_state == s.honest_nodes_states[vpn].attestation_consensus_engine_state;
                assert inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc(s, vpn, cid);

                attestation_duty, attestation_slashing_db :| inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_body(cid, attestation_duty, attestation_slashing_db, vp);
            }

            assert inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_body(cid, attestation_duty, attestation_slashing_db, vp);


        }

    }  

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist(
        s: DVState,
        event: DV.Event,
        s': DVState
    )   
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')    
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist(s)
    requires inv_quorum_constraints(s)
    requires inv_unchanged_honesty(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)      
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc(s)  
    ensures inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist(s')   
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                forall hn, cid: nat, vp |
                    && hn in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions.Keys
                    && vp in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions[hn]
                ensures exists attestation_duty, attestation_slashing_db :: inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_body(cid, attestation_duty, attestation_slashing_db, vp)
                {
                    var attestation_duty: AttestationDuty, attestation_slashing_db := lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_helper(s, event, s', cid, hn, vp);
                }
                assert inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist(s');

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                assert inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist(s');
        }
    }   

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_updateConsensusInstanceValidityCheckHelper(
        m: map<Slot, DVC_Spec_NonInstr.AttestationConsensusValidityCheckState>,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        m': map<Slot, DVC_Spec_NonInstr.AttestationConsensusValidityCheckState>
    )    
    requires m' == updateConsensusInstanceValidityCheckHelper(m, new_attestation_slashing_db)
    requires forall k | k in m :: inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2_body_body(k, m[k].attestation_duty, m[k].validityPredicate)
    ensures forall k | k in m' :: inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2_body_body(k, m'[k].attestation_duty, m'[k].validityPredicate)    
    {
        forall k | k in  m 
        ensures k in m'
        {
            lemmaMapKeysHasOneEntryInItems(m, k);
            assert k in m';
        }

        assert m.Keys == m'.Keys;

        forall k | k in m' 
        ensures inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_body(k, m'[k].attestation_duty, new_attestation_slashing_db, m'[k].validityPredicate); 
        {
            assert m'[k] == m[k].(
                    validityPredicate := (ad: AttestationData) => consensus_is_valid_attestation_data(new_attestation_slashing_db, ad, m[k].attestation_duty)
            );
            assert  inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_body(k, m'[k].attestation_duty, new_attestation_slashing_db, m'[k].validityPredicate);        
        }
    }

    
    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty_updateConsensusInstanceValidityCheck(
        s: ConsensusEngineState,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState
    )    
    requires s' == updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db)
    ensures s'.active_attestation_consensus_instances.Keys == s.active_attestation_consensus_instances.Keys
    ensures s'.att_slashing_db_hist.Keys == s.att_slashing_db_hist.Keys + s'.active_attestation_consensus_instances.Keys;
    // requires forall k | k in m :: inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2_body_body(k, m[k].attestation_duty, m[k].validityPredicate)
    // ensures forall k | k in m' :: inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2_body_body(k, m'[k].attestation_duty, m'[k].validityPredicate)    
    {
        lem_updateConsensusInstanceValidityCheckHelper(s.active_attestation_consensus_instances, new_attestation_slashing_db, s'.active_attestation_consensus_instances);

        assert s'.att_slashing_db_hist.Keys == s.att_slashing_db_hist.Keys + s'.active_attestation_consensus_instances.Keys;

        assert forall slot, vp: AttestationData -> bool |
                    && slot in s.att_slashing_db_hist.Keys 
                    && vp in s.att_slashing_db_hist[slot].Keys
                    ::
                    && s.att_slashing_db_hist.Keys <= s'.att_slashing_db_hist.Keys
                    && s.att_slashing_db_hist[slot].Keys <= s'.att_slashing_db_hist[slot].Keys
                    && s.att_slashing_db_hist[slot][vp] <= s'.att_slashing_db_hist[slot][vp]
        ;

        assert forall slot |
                    && slot in s'.active_attestation_consensus_instances.Keys 
                    && slot in s.att_slashing_db_hist.Keys
                    && var vp := s'.active_attestation_consensus_instances[slot].validityPredicate;
                    && vp in s.att_slashing_db_hist[slot].Keys
                    ::
                    var vp := s'.active_attestation_consensus_instances[slot].validityPredicate;
                    s.att_slashing_db_hist[slot][vp] + {new_attestation_slashing_db} == s'.att_slashing_db_hist[slot][vp];      

        assert forall slot, vp: AttestationData -> bool |
                    && slot in s'.att_slashing_db_hist.Keys 
                    && slot !in s.att_slashing_db_hist.Keys 
                    && vp in s'.att_slashing_db_hist[slot].Keys
                    ::
                    && vp == s'.active_attestation_consensus_instances[slot].validityPredicate
        ;      

        assert forall slot, vp: AttestationData -> bool |
                    && slot in s.att_slashing_db_hist.Keys 
                    && vp in s'.att_slashing_db_hist[slot].Keys
                    && vp !in s.att_slashing_db_hist[slot].Keys
                    ::
                    && s'.att_slashing_db_hist[slot][vp] == {new_attestation_slashing_db}
        ;     
                   
    }   

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty_updateConsensusInstanceValidityCheck2(
        s: ConsensusEngineState,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState,
        slot: nat,
        vp: AttestationData -> bool 
    )    
    requires s' == updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db)
    requires 
                    && slot in s'.active_attestation_consensus_instances.Keys 
                    && slot in s.att_slashing_db_hist.Keys
                    && vp == s'.active_attestation_consensus_instances[slot].validityPredicate
                    && vp in s.att_slashing_db_hist[slot].Keys  
    ensures s.att_slashing_db_hist[slot][vp] + {new_attestation_slashing_db} == s'.att_slashing_db_hist[slot][vp];      
    {
        lem_updateConsensusInstanceValidityCheckHelper(s.active_attestation_consensus_instances, new_attestation_slashing_db, s'.active_attestation_consensus_instances);

        assert s'.att_slashing_db_hist.Keys == s.att_slashing_db_hist.Keys + s'.active_attestation_consensus_instances.Keys;                   
    }   

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty_updateConsensusInstanceValidityCheck3(
        s: ConsensusEngineState,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState,
        slot: nat,
        vp: AttestationData -> bool 
    )    
    requires s' == updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db)
    requires 
                    && slot in s'.active_attestation_consensus_instances.Keys 
                    && slot in s.att_slashing_db_hist.Keys
                    && vp != s'.active_attestation_consensus_instances[slot].validityPredicate
                    && vp in s.att_slashing_db_hist[slot].Keys  
    ensures s.att_slashing_db_hist[slot][vp] == s'.att_slashing_db_hist[slot][vp];      
    {
        lem_updateConsensusInstanceValidityCheckHelper(s.active_attestation_consensus_instances, new_attestation_slashing_db, s'.active_attestation_consensus_instances);

        assert s'.att_slashing_db_hist.Keys == s.att_slashing_db_hist.Keys + s'.active_attestation_consensus_instances.Keys;                   
    }      

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty_updateConsensusInstanceValidityCheck4(
        s: ConsensusEngineState,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState,
        slot: nat,
        vp: AttestationData -> bool 
    )    
    requires s' == updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db)
    requires 
                    && slot !in s'.active_attestation_consensus_instances.Keys 
                    && slot in s.att_slashing_db_hist.Keys
                    && vp in s.att_slashing_db_hist[slot].Keys  
    ensures s.att_slashing_db_hist[slot][vp] == s'.att_slashing_db_hist[slot][vp];      
    {
        lem_updateConsensusInstanceValidityCheckHelper(s.active_attestation_consensus_instances, new_attestation_slashing_db, s'.active_attestation_consensus_instances);

        assert s'.att_slashing_db_hist.Keys == s.att_slashing_db_hist.Keys + s'.active_attestation_consensus_instances.Keys;                   
    }   

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty_updateConsensusInstanceValidityCheck5(
        s: ConsensusEngineState,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        s': ConsensusEngineState,
        slot: nat    
    )    
    requires s' == updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db)
    requires slot in s.att_slashing_db_hist.Keys
    ensures slot in s'.att_slashing_db_hist.Keys
    ensures s.att_slashing_db_hist[slot].Keys <= s'.att_slashing_db_hist[slot].Keys;      
    {
        lem_updateConsensusInstanceValidityCheckHelper(s.active_attestation_consensus_instances, new_attestation_slashing_db, s'.active_attestation_consensus_instances);

        assert s'.att_slashing_db_hist.Keys == s.att_slashing_db_hist.Keys + s'.active_attestation_consensus_instances.Keys;                   
    }                

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_f_serve_attestation_duty(
        process: DVCState,
        attestation_duty: AttestationDuty,
        s': DVCState
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state  
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2(process) 
    ensures inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2(s'); 
    {
        var s_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );
        assert inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2(s_mod); 
        lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_f_check_for_next_queued_duty(s_mod, s');        
    }    

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_f_check_for_next_queued_duty(
        process: DVCState,
        s': DVCState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state   
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2(process) 
    ensures inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2(s'); 
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

                lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_updateConsensusInstanceValidityCheckHelper(
                        process.attestation_consensus_engine_state.active_attestation_consensus_instances,
                        new_attestation_slashing_db,
                        s_mod.attestation_consensus_engine_state.active_attestation_consensus_instances
                );

                lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_f_check_for_next_queued_duty(s_mod, s');

            }
            else 
            {
                var attestation_duty := process.attestation_duties_queue[0];
                var attestation_slashing_db := process.attestation_slashing_db;

                var acvc := DVC_Spec_NonInstr.AttestationConsensusValidityCheckState(
                    attestation_duty := attestation_duty,
                    validityPredicate := (ad: AttestationData) => consensus_is_valid_attestation_data(attestation_slashing_db, ad, attestation_duty)
                );     

                assert s'.attestation_consensus_engine_state.active_attestation_consensus_instances == process.attestation_consensus_engine_state.active_attestation_consensus_instances[attestation_duty.slot := acvc];

                forall cid | 
                    && cid in s'.attestation_consensus_engine_state.active_attestation_consensus_instances  
                ensures inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2_body(s', cid); 
                {
                    if cid != attestation_duty.slot 
                    {
                        assert cid in process.attestation_consensus_engine_state.active_attestation_consensus_instances;
                        assert inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2_body(s', cid); 
                    }
                    else 
                    {
                        assert inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_body(
                            cid,
                            attestation_duty,
                            attestation_slashing_db,
                            acvc.validityPredicate
                        );
                        assert inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2_body(s', cid); 
                    }
                }              

                assert inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2(s'); 
            }
        } 
        else 
        {
            assert inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2(s'); 
        }       
    }

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_f_att_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(process, id, decided_attestation_data).state
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2(process) 
    ensures inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2(s'); 
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

        lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_updateConsensusInstanceValidityCheckHelper(
                process.attestation_consensus_engine_state.active_attestation_consensus_instances,
                attestation_slashing_db,
                s_mod.attestation_consensus_engine_state.active_attestation_consensus_instances
        );            

        lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_f_check_for_next_queued_duty(s_mod, s');             
    }     

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        s': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2(process) 
    ensures inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2(s');     
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

            lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_updateConsensusInstanceValidityCheckHelper(
                    process.attestation_consensus_engine_state.active_attestation_consensus_instances,
                    new_attestation_slashing_db,
                    s_mod.attestation_consensus_engine_state.active_attestation_consensus_instances
            ); 

            lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_f_check_for_next_queued_duty(s_mod, s');             
           
        }
    }      

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc(
        s: DVState,
        event: DV.Event,
        s': DVState
    )   
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')    
    requires inv_quorum_constraints(s)
    requires inv_unchanged_honesty(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)      
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc(s)  
    ensures inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc(s')    
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        forall n | n in s'.honest_nodes_states
                        ensures inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2(s'.honest_nodes_states[n]); 
                        {
                            if n == node
                            {
                                lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_f_serve_attestation_duty(s_node, attestation_duty, s'_node);
                                assert inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2(s'_node); 
                            }
                        }
                        assert inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc(s');                        
                  
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        forall n | n in s'.honest_nodes_states
                        ensures inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2(s'.honest_nodes_states[n]); 
                        {
                            if n == node
                            {
                                lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_f_att_consensus_decided(s_node, id, decided_attestation_data, s'_node);
                                assert inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2(s'_node); 
                            }
                        }
                        assert inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc(s');                       
              
                    case ReceivedAttestationShare(attestation_share) => 
                        forall n | n in s'.honest_nodes_states
                        ensures s'.honest_nodes_states[n].attestation_consensus_engine_state == s.honest_nodes_states[n].attestation_consensus_engine_state
                        {
                            if n == node
                            {
                                lem_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                            }
                        }
                        assert inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc(s');     

                    case ImportedNewBlock(block) => 
                        forall n | n in s'.honest_nodes_states
                        ensures inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2(s'.honest_nodes_states[n]); 
                        {
                            if n == node
                            {
                                var s_node := add_block_to_bn(s_node, nodeEvent.block);
                                lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_f_listen_for_new_imported_blocks(s_node, block, s'_node);
                                assert inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc_single_dvc_2(s'_node); 
                            }
                        }
                        assert inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc(s');                        
               
                    case ResendAttestationShares => 
                        assert inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc(s');
                   
                    case NoEvent => 
                        assert inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc(s');
                }            


            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                assert inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc(s');
        }        
    }   

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_serve_attestation_duty(
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
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(dv, process)
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv, n, process)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_queued_att_duties_are_from_dv_seq_of_att_duties_body_body(dv, n, process, index_next_attestation_duty_to_be_served-1)
    requires inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, process)    
    requires inv_head_attetation_duty_queue_higher_than_latest_attestation_duty_body_body(process) 
    requires is_sequence_attestation_duties_to_be_served_orderd(dv);
    requires inv_attestation_duty_queue_is_ordered_body_body(process) 
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)  
    requires lem_ServeAttstationDuty2_predicate(dv, index_next_attestation_duty_to_be_served, attestation_duty, n)
    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(dv, s');  
    {
        var new_p := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
        );

        if process.attestation_duties_queue != []
        {
            assert inv_head_attetation_duty_queue_higher_than_latest_attestation_duty_body_body(new_p);
            assert inv_attestation_duty_queue_is_ordered_body_body(new_p); 
        }
        else 
        {
            assert inv_attestation_duty_queue_is_ordered_body_body(new_p); 
            assert inv_head_attetation_duty_queue_higher_than_latest_attestation_duty_body_body(new_p);
        }

        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty(new_p, s', dv, n, index_next_attestation_duty_to_be_served);

    }     

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_att_consensus_decided(
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
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(dv, process)
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv, n, process)
    requires inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, process)    
    requires inv_head_attetation_duty_queue_higher_than_latest_attestation_duty_body_body(process) 
    requires inv_attestation_duty_queue_is_ordered_body_body(process) 
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process) 
    requires dv.consensus_on_attestation_data[id].decided_value.isPresent()
    requires dv.consensus_on_attestation_data[id].decided_value.safe_get() ==  decided_attestation_data
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)
    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(dv, s');  
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

            lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty_updateConsensusInstanceValidityCheck(
                process.attestation_consensus_engine_state,
                attestation_slashing_db,
                s_mod.attestation_consensus_engine_state
            );           

            // assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, s_mod);   
            forall s1: nat, s2: nat, vp, db2 |
                && s1 in s_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
                && s2 in s_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys            
                && s1 < s2       
                && vp in s_mod.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys   
                && db2 in s_mod.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp]  
            ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body_body(dv, s1, db2)
            {
                assert  || s2 in process.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                        || s2 in process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;
                assert s2 in process.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                assert s1 in process.attestation_consensus_engine_state.att_slashing_db_hist.Keys;

                assert dv.consensus_on_attestation_data[s1].decided_value.isPresent();
                var decided_a_data := dv.consensus_on_attestation_data[s1].decided_value.safe_get();
                var sdba := construct_SlashingDBAttestation_from_att_data(decided_a_data);  

                assert 
                    && vp in process.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys 
                    && db2 in process.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp]
                    ==>
                    inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body_body(dv, s1, db2);   

                if vp !in process.attestation_consensus_engine_state.att_slashing_db_hist[s2]
                {
                    assert s_mod.attestation_consensus_engine_state.active_attestation_consensus_instances[s2].validityPredicate == vp;
                    assert s_mod.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp] ==  {attestation_slashing_db};
                    assert sdba in db2;
                }
                else 
                {
                    if s2 in s_mod.attestation_consensus_engine_state.active_attestation_consensus_instances
                    {
                        if vp == s_mod.attestation_consensus_engine_state.active_attestation_consensus_instances[s2].validityPredicate
                        {
                            lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty_updateConsensusInstanceValidityCheck2(
                                process.attestation_consensus_engine_state,
                                attestation_slashing_db,
                                s_mod.attestation_consensus_engine_state,
                                s2,
                                vp
                            );
                            assert sdba in db2;
                        }
                        else 
                        {
                            lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty_updateConsensusInstanceValidityCheck3(
                                process.attestation_consensus_engine_state,
                                attestation_slashing_db,
                                s_mod.attestation_consensus_engine_state,
                                s2,
                                vp
                            );
                            assert sdba in db2;
                        }
                    }
                    else 
                    {
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty_updateConsensusInstanceValidityCheck4(
                            process.attestation_consensus_engine_state,
                            attestation_slashing_db,
                            s_mod.attestation_consensus_engine_state,
                            s2,
                            vp
                        );
                        assert sdba in db2;
                    }
                }
                assert sdba in db2;
                assert  inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body_body(dv, s1, db2);
            }    

            lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty(s_mod, s', dv, n, index_next_attestation_duty_to_be_served);    
        }         
    }  

    lemma lem_f_listen_for_new_imported_blocks_helper_1(
        dv: DVState,
        process: DVCState,
        block: BeaconBlock,
        new_consensus_instances_already_decided: map<Slot, AttestationData>
    )
    requires f_listen_for_new_imported_blocks_helper_1.requires(process, block)
    requires new_consensus_instances_already_decided == f_listen_for_new_imported_blocks_helper_1(process, block)
    requires concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv)
    requires pred_data_of_att_share_is_decided_value(dv)
    requires pred_axiom_is_my_attestation_2(dv, process, block)
    ensures 
        forall slot | 
                slot in new_consensus_instances_already_decided
                :: 
                && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
                && dv.consensus_on_attestation_data[slot].decided_value.safe_get() == new_consensus_instances_already_decided[slot]
                ;  
    {
        forall slot | slot in new_consensus_instances_already_decided
        ensures 
            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
            && dv.consensus_on_attestation_data[slot].decided_value.safe_get() == new_consensus_instances_already_decided[slot]
            ;         
        {

            var valIndex := bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);


            var a :| 
                && a in block.body.attestations
                && DVC_Spec_NonInstr.isMyAttestation(a, process.bn, block, valIndex)
                && a.data == new_consensus_instances_already_decided[slot]
            ;

            var a' :|
                && a' in dv.all_attestations_created
                && a'.data == a.data 
                && is_valid_attestation(a', dv.dv_pubkey);    

            var hn', att_share: AttestationShare :| concl_exists_honest_dvc_that_sent_att_share_for_submitted_att_body(dv, hn', att_share, a');

            assert
            && dv.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent()
            && dv.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;

            assert
            && dv.consensus_on_attestation_data[slot].decided_value.isPresent()
            && dv.consensus_on_attestation_data[slot].decided_value.safe_get() == new_consensus_instances_already_decided[slot]
            ;              
        }
    }       

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        s': DVCState,
        dv': DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(dv', process)
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(dv', n, process, index_next_attestation_duty_to_be_served)
    requires inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv', n, process)
    requires inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv', n, process)    
    requires inv_head_attetation_duty_queue_higher_than_latest_attestation_duty_body_body(process) 
    requires inv_attestation_duty_queue_is_ordered_body_body(process) 
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process) 
    requires inv_g_d_a_body_body(dv', n, process)  
    requires inv_g_d_b_body_body(dv', n, process)   
    requires pred_inv_current_latest_attestation_duty_match_body_body(process)
    requires concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv')
    requires pred_data_of_att_share_is_decided_value(dv')
    requires pred_axiom_is_my_attestation_2(dv', process, block)
    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(dv', s');  
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

            lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty_updateConsensusInstanceValidityCheck(
                new_process.attestation_consensus_engine_state,
                new_attestation_slashing_db,
                s_mod.attestation_consensus_engine_state
            );    

            assert att_consensus_instances_already_decided == process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

            if decided_attestation_data in new_consensus_instances_already_decided.Values
            {
                forall an |
                    && an in dv'.sequence_attestation_duties_to_be_served.Values 
                    && an.node == n 
                    && an.attestation_duty.slot < get_upperlimit_decided_instances(s_mod)
                ensures 
                    var slot := an.attestation_duty.slot;
                    && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                    && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db                    
                {
                    if an.attestation_duty.slot < s_mod.latest_attestation_duty.safe_get().slot 
                    {
                        var slot := an.attestation_duty.slot;
                        assert
                        && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                        ;
                    }
                    else 
                    {
                        var slot := an.attestation_duty.slot;

                        lem_f_listen_for_new_imported_blocks_helper_1(
                            dv',
                            process,
                            block,
                            new_consensus_instances_already_decided
                        );

                        assert
                        && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                        ;                        
                    }
                } 
                assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv', n, s_mod);                   
            }
            else 
            {
                assert decided_attestation_data in process.future_att_consensus_instances_already_decided.Values;

                assert decided_attestation_data == process.future_att_consensus_instances_already_decided[new_process.current_attestation_duty.safe_get().slot];

                forall an |
                    && an in dv'.sequence_attestation_duties_to_be_served.Values 
                    && an.node == n 
                    && an.attestation_duty.slot < get_upperlimit_decided_instances(s_mod)
                ensures 
                    var slot := an.attestation_duty.slot;
                    && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                    && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                    ;                      
                {
                    if an.attestation_duty.slot < s_mod.latest_attestation_duty.safe_get().slot 
                    {
                        var slot := an.attestation_duty.slot;
                        assert
                        && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                        ;
                    }
                    else 
                    {
                        assert an.attestation_duty.slot == s_mod.latest_attestation_duty.safe_get().slot;

                        var slot := an.attestation_duty.slot;
                        assert slot in process.future_att_consensus_instances_already_decided;
                        assert
                        && dv'.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && construct_SlashingDBAttestation_from_att_data(dv'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_mod.attestation_slashing_db
                        ;                        
                    }
                }

                assert inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv', n, s_mod);
            }

            forall s1: nat, s2: nat, vp, db2 |
                && s1 in s_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
                && s2 in s_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys            
                && s1 < s2       
                && vp in s_mod.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys   
                && db2 in s_mod.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp]  
            ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body_body(dv', s1, db2)
            {
                assert  || s2 in new_process.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                        || s2 in new_process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;
                assert s2 in new_process.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                assert s1 in new_process.attestation_consensus_engine_state.att_slashing_db_hist.Keys;

                assert dv'.consensus_on_attestation_data[s1].decided_value.isPresent();
                var decided_a_data := dv'.consensus_on_attestation_data[s1].decided_value.safe_get();
                var sdba := construct_SlashingDBAttestation_from_att_data(decided_a_data);  

                assert 
                    && vp in new_process.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys 
                    && db2 in new_process.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp]
                    ==>
                    inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body_body(dv', s1, db2);   

                if vp !in new_process.attestation_consensus_engine_state.att_slashing_db_hist[s2]
                {
                    assert s_mod.attestation_consensus_engine_state.active_attestation_consensus_instances[s2].validityPredicate == vp;
                    assert s_mod.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp] ==  {new_attestation_slashing_db};
                    assert sdba in db2;
                }
                else 
                {
                    if s2 in s_mod.attestation_consensus_engine_state.active_attestation_consensus_instances
                    {
                        if vp == s_mod.attestation_consensus_engine_state.active_attestation_consensus_instances[s2].validityPredicate
                        {
                            lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty_updateConsensusInstanceValidityCheck2(
                                new_process.attestation_consensus_engine_state,
                                new_attestation_slashing_db,
                                s_mod.attestation_consensus_engine_state,
                                s2,
                                vp
                            );
                            assert sdba in db2;
                        }
                        else 
                        {
                            lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty_updateConsensusInstanceValidityCheck3(
                                new_process.attestation_consensus_engine_state,
                                new_attestation_slashing_db,
                                s_mod.attestation_consensus_engine_state,
                                s2,
                                vp
                            );
                            assert sdba in db2;
                        }
                    }
                    else 
                    {
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty_updateConsensusInstanceValidityCheck4(
                            new_process.attestation_consensus_engine_state,
                            new_attestation_slashing_db,
                            s_mod.attestation_consensus_engine_state,
                            s2,
                            vp
                        );
                        assert sdba in db2;
                    }
                }
                assert sdba in db2;
                assert  inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body_body(dv', s1, db2);
            }                

            lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty(s_mod, s', dv', n, index_next_attestation_duty_to_be_served);                    
        }        
    }          

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty(
        process: DVCState,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey,
        index_next_attestation_duty_to_be_served: nat
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state   
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(dv, process)
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(dv, n, process, index_next_attestation_duty_to_be_served)
    requires inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(dv, n, process)
    requires inv_inv_decided_values_of_previous_duties_are_known_body_body_new(dv, n, process)    
    requires inv_head_attetation_duty_queue_higher_than_latest_attestation_duty_body_body(process) 
    requires inv_attestation_duty_queue_is_ordered_body_body(process) 
    requires inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist_body_body(process)   
    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(dv, s');  
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

                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty_updateConsensusInstanceValidityCheck(
                    process.attestation_consensus_engine_state,
                    new_attestation_slashing_db,
                    s_mod.attestation_consensus_engine_state
                );

                // assert 

                forall s1: nat, s2: nat, vp, db2 |
                    && s1 in s_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
                    && s2 in s_mod.attestation_consensus_engine_state.att_slashing_db_hist.Keys            
                    && s1 < s2       
                    && vp in s_mod.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys   
                    && db2 in s_mod.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp]  
                ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body_body(dv, s1, db2)
                {
                    assert  || s2 in process.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                            || s2 in process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;
                    assert s2 in process.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
                    assert s1 in process.attestation_consensus_engine_state.att_slashing_db_hist.Keys;

                    assert dv.consensus_on_attestation_data[s1].decided_value.isPresent();
                    var decided_a_data := dv.consensus_on_attestation_data[s1].decided_value.safe_get();
                    var sdba := construct_SlashingDBAttestation_from_att_data(decided_a_data);  

                    assert 
                        && vp in process.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys 
                        && db2 in process.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp]
                        ==>
                        inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body_body(dv, s1, db2);   

                    if vp !in process.attestation_consensus_engine_state.att_slashing_db_hist[s2]
                    {
                        assert s_mod.attestation_consensus_engine_state.active_attestation_consensus_instances[s2].validityPredicate == vp;
                        assert s_mod.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp] ==  {new_attestation_slashing_db};
                        assert sdba in db2;
                    }
                    else 
                    {
                        if s2 in s_mod.attestation_consensus_engine_state.active_attestation_consensus_instances
                        {
                            if vp == s_mod.attestation_consensus_engine_state.active_attestation_consensus_instances[s2].validityPredicate
                            {
                                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty_updateConsensusInstanceValidityCheck2(
                                    process.attestation_consensus_engine_state,
                                    new_attestation_slashing_db,
                                    s_mod.attestation_consensus_engine_state,
                                    s2,
                                    vp
                                );
                                assert sdba in db2;
                            }
                            else 
                            {
                                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty_updateConsensusInstanceValidityCheck3(
                                    process.attestation_consensus_engine_state,
                                    new_attestation_slashing_db,
                                    s_mod.attestation_consensus_engine_state,
                                    s2,
                                    vp
                                );
                                assert sdba in db2;
                            }
                        }
                        else 
                        {
                            lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty_updateConsensusInstanceValidityCheck4(
                                process.attestation_consensus_engine_state,
                                new_attestation_slashing_db,
                                s_mod.attestation_consensus_engine_state,
                                s2,
                                vp
                            );
                            assert sdba in db2;
                        }
                    }
                    assert sdba in db2;
                    assert  inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body_body(dv, s1, db2);
                }                       

                assert inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(dv, s_mod); 

                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_check_for_next_queued_duty(s_mod, s', dv, n, index_next_attestation_duty_to_be_served);

                assert inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(dv, s');

            }
            else 
            {
                var new_process := process.(
                    attestation_duties_queue := process.attestation_duties_queue[1..]
                );                  
                assert s'.latest_attestation_duty == Some( process.attestation_duties_queue[0]);

      

                if process.latest_attestation_duty.isPresent()
                {
                    assert inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(dv, s');           
                }  
                else 
                {
                    assert inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(dv, s');
                } 
                
            }
        } 
        else 
        {
            assert inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(dv, s');
        }       
    }  

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')    
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values(s)
    requires invNetwork(s)
    requires inv_quorum_constraints(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_queued_att_duty_is_rcvd_duty3(s)
    ensures forall ci: nat ::
            var s_consensus := s.consensus_on_attestation_data[ci];
            var s'_consensus := s.consensus_on_attestation_data[ci];
            && (s_consensus.decided_value.isPresent() ==> s'_consensus.decided_value.isPresent())
            && (s_consensus.decided_value.isPresent() ==> 
                    s_consensus.decided_value.safe_get() == s'_consensus.decided_value.safe_get())     
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                forall ci: nat 
                ensures var s_consensus := s.consensus_on_attestation_data[ci];
                        var s'_consensus := s.consensus_on_attestation_data[ci];
                        && (s_consensus.decided_value.isPresent() ==> s'_consensus.decided_value.isPresent())
                        && (s_consensus.decided_value.isPresent() ==> 
                                s_consensus.decided_value.safe_get() == s'_consensus.decided_value.safe_get())               
                {
                    var s_consensus := s.consensus_on_attestation_data[ci];
                    var s'_consensus := s.consensus_on_attestation_data[ci];
                    assert isConditionForSafetyTrue(s_consensus);

                    assert s_consensus.decided_value.isPresent() ==> s'_consensus.decided_value.isPresent();
                    assert s_consensus.decided_value.isPresent() ==> 
                                s_consensus.decided_value.safe_get() == s'_consensus.decided_value.safe_get();
                    
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>

        }        
    }

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper2(
        s: DVState,
        event: DV.Event,
        s': DVState,
        ci: nat
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires invNetwork(s)
    requires inv_quorum_constraints(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_queued_att_duty_is_rcvd_duty3(s)
    requires s.consensus_on_attestation_data[ci].decided_value.isPresent()
    ensures 
            var s_consensus := s.consensus_on_attestation_data[ci];
            var s'_consensus := s.consensus_on_attestation_data[ci];
            && (s'_consensus.decided_value.isPresent())
            && (s_consensus.decided_value.safe_get() == s'_consensus.decided_value.safe_get())     
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>

                    var s_consensus := s.consensus_on_attestation_data[ci];
                    var s'_consensus := s.consensus_on_attestation_data[ci];
                    assert isConditionForSafetyTrue(s_consensus);

                    // assert s_consensus.decided_value.isPresent() ==> s'_consensus.decided_value.isPresent();
                    // assert s_consensus.decided_value.isPresent() ==> 
                    //             s_consensus.decided_value.safe_get() == s'_consensus.decided_value.safe_get();


            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>

        }        
    }    

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCState
    )
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(s, s_node)
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values(s)
    requires invNetwork(s)
    requires inv_quorum_constraints(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_queued_att_duty_is_rcvd_duty3(s)  
    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(s', s_node)  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        forall s1: nat, s2: nat, vp, db2 |
            && s1 in s_node.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
            && s2 in s_node.attestation_consensus_engine_state.att_slashing_db_hist.Keys            
            && s1 < s2       
            && vp in s_node.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys   
            && db2 in s_node.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp]           
        ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body_body(s', s1, db2);
        {
            assert inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body_body(s, s1, db2);
            lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper2(s, event, s', s1);
            // assert s.consensus_on_attestation_data[s1].decided_value.isPresent();
            assert s'.consensus_on_attestation_data[s1].decided_value.isPresent();
            assert inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body_body(s', s1, db2);
        }           
        
    }     

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3a(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCState,
        n: BLSPubkey
    )
    requires inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s, n, s_node)
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values(s)
    requires invNetwork(s)
    requires inv_quorum_constraints(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_queued_att_duty_is_rcvd_duty3(s)  
    ensures inv_inv_decided_values_of_previous_duties_are_known_body_body_new(s', n, s_node)  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        forall an |
            && an in s'.sequence_attestation_duties_to_be_served.Values 
            && an.node == n 
            && an.attestation_duty.slot < get_upperlimit_decided_instances(s_node)    
        ensures 
                var slot := an.attestation_duty.slot;
                && s'.consensus_on_attestation_data[slot].decided_value.isPresent()
                && construct_SlashingDBAttestation_from_att_data(s'.consensus_on_attestation_data[slot].decided_value.safe_get()) in s_node.attestation_slashing_db
                                           
        // ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body_body(s', s1, db2);
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


    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3c(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCState,
        n: BLSPubkey
    )
    requires inv_g_d_a_body_body(s, n, s_node)
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values(s)
    requires invNetwork(s)
    requires inv_quorum_constraints(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_queued_att_duty_is_rcvd_duty3(s)  
    ensures inv_g_d_a_body_body(s', n, s_node)  
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        forall slot |
            && slot in s_node.future_att_consensus_instances_already_decided
        ensures
            && s'.consensus_on_attestation_data[slot].decided_value.isPresent();
        ensures
            && s_node.future_att_consensus_instances_already_decided[slot] == s'.consensus_on_attestation_data[slot].decided_value.safe_get()
            ;                
        {
            lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper2(s, event, s', slot);

            assert
                && s.consensus_on_attestation_data[slot].decided_value.isPresent()
                && s_node.future_att_consensus_instances_already_decided[slot] == s.consensus_on_attestation_data[slot].decided_value.safe_get()
                ;                        

            assert
                && s'.consensus_on_attestation_data[slot].decided_value.isPresent();
            assert
                && s_node.future_att_consensus_instances_already_decided[slot] == s'.consensus_on_attestation_data[slot].decided_value.safe_get()
                ;                       
        }           
        
    }             

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper4(
        s: DVState,
        event: DV.Event,
        s': DVState,
        s_node: DVCState,
        n: BLSPubkey
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')    
    requires inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(s, n, s_node, s.index_next_attestation_duty_to_be_served)
    requires inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s, n, s_node)
    requires inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s, n, s_node, s.index_next_attestation_duty_to_be_served)
    requires inv_queued_att_duties_are_from_dv_seq_of_att_duties_body_body(s, n, s_node, s.index_next_attestation_duty_to_be_served)
    requires inv_g_d_b_body_body(s, n, s_node)


    ensures inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(s', n, s_node, s.index_next_attestation_duty_to_be_served)
    ensures inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s', n, s_node)
    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', n, s_node, s.index_next_attestation_duty_to_be_served)
    ensures inv_queued_att_duties_are_from_dv_seq_of_att_duties_body_body(s', n, s_node, s.index_next_attestation_duty_to_be_served)    
    ensures inv_g_d_b_body_body(s', n, s_node)    


    // requires inv_db_of_validity_predicate_contains_all_previous_decided_values(s)
    // requires invNetwork(s)
    // requires inv_quorum_constraints(s)
    // requires inv_only_dv_construct_signed_attestation_signature(s)
    // requires inv_queued_att_duty_is_rcvd_duty3(s)  
    // ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(s', s_node)  
    {
        assert s'.index_next_attestation_duty_to_be_served <= s'.index_next_attestation_duty_to_be_served <= s'.index_next_attestation_duty_to_be_served + 1;

        assert inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_body_body(s', n, s_node, s.index_next_attestation_duty_to_be_served);
        assert inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_att_duty(s', n, s_node);
        assert inv_db_of_validity_predicate_contains_all_previous_decided_values_b_body_body(s', n, s_node, s.index_next_attestation_duty_to_be_served);
        assert inv_queued_att_duties_are_from_dv_seq_of_att_duties_body_body(s', n, s_node, s.index_next_attestation_duty_to_be_served);

        
    }      

    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper5(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event.event.AttConsensusDecided?
    requires inv_quorum_constraints(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_queued_att_duty_is_rcvd_duty3(s)    
    ensures s'.consensus_on_attestation_data[event.event.id].decided_value.isPresent(); 
    ensures  s'.consensus_on_attestation_data[event.event.id].decided_value.safe_get() == event.event.decided_attestation_data;    
    {
        var s_w_honest_node_states_updated := lem_inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_get_s_w_honest_node_states_updated(s, event.node, event.event);           
        var cid := event.event.id;

        assert s_w_honest_node_states_updated.consensus_on_attestation_data == s.consensus_on_attestation_data;


        var output := Some(Decided(event.node, event.event.decided_attestation_data)); 

        var validityPredicates := 
            map n |
                    && n in s_w_honest_node_states_updated.honest_nodes_states.Keys 
                    && cid in s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
                ::
                    s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances[cid].validityPredicate
            ;

        var s_consensus := s_w_honest_node_states_updated.consensus_on_attestation_data[cid];
        var s'_consensus := s'.consensus_on_attestation_data[cid];                

        assert
            ConsensusSpec.Next(
                s_consensus,
                validityPredicates,
                s'_consensus,
                output
            );                                       
    }    


    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper6(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires event.HonestNodeTakingStep?
    requires event.event.AttConsensusDecided?
    requires inv_quorum_constraints(s)
    requires inv_unchanged_honesty(s)
    requires inv_only_dv_construct_signed_attestation_signature(s)
    requires inv_queued_att_duty_is_rcvd_duty3(s)    
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist(s)
    requires inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc(s)      
    requires inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)      
    ensures s'.consensus_on_attestation_data[event.event.id].decided_value.isPresent(); 
    ensures  s'.consensus_on_attestation_data[event.event.id].decided_value.safe_get() == event.event.decided_attestation_data;   
    ensures  s'.consensus_on_attestation_data[event.event.id].decided_value.safe_get().slot == event.event.id;    
    ensures event.event.decided_attestation_data.slot == event.event.id
    {
        lem_inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s, event, s');
        assert inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s');
        assert s'.consensus_on_attestation_data[event.event.id].decided_value.isPresent(); 
        assert  s'.consensus_on_attestation_data[event.event.id].decided_value.safe_get() == event.event.decided_attestation_data;   
        assert  s'.consensus_on_attestation_data[event.event.id].decided_value.safe_get().slot == event.event.id;   
        assert event.event.decided_attestation_data.slot == event.event.id;         
    }    

    predicate lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_precond(
        s: DVState     
    ) 
    {
        && inv_db_of_validity_predicate_contains_all_previous_decided_values(s)
        && construct_signed_attestation_signature_assumptions_helper(
            s.construct_signed_attestation_signature,
            s.dv_pubkey,
            s.all_nodes
        )
        && invNetwork(s)
        && inv_quorum_constraints(s)
        && inv_unchanged_honesty(s)
        && inv_only_dv_construct_signed_attestation_signature(s)
        && inv_queued_att_duty_is_rcvd_duty3(s)
        && inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist(s)
        && inv_exists_att_duty_in_dv_seq_of_att_duty_for_every_slot_in_att_slashing_db_hist_a(s)
        && inv_db_of_validity_predicate_contains_all_previous_decided_values_b(s)
        && inv_db_of_validity_predicate_contains_all_previous_decided_values_c(s)
        && inv_decided_values_of_previous_duties_are_known_new(s)
        && inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(s) 
        && is_sequence_attestation_duties_to_be_served_orderd(s)
        && inv_attestation_duty_queue_is_ordered(s) 
        && inv_active_attestation_consensus_instances_keys_is_subset_of_att_slashing_db_hist(s)      
        && pred_inv_current_latest_attestation_duty_match(s)
        && concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s)
        && pred_data_of_att_share_is_decided_value(s)
        && inv_decided_value_of_consensus_instance_is_decided_by_quorum(s)  
        && inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(s)    
        && inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist(s)    
        && inv_sent_validity_predicate_is_based_on_rcvd_duty_and_slashing_db_in_hist_for_dvc(s)  
        && inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)  
        && inv_g_d_a(s)
        && inv_g_d_b(s)   
        && pred_rcvd_attestation_shares_is_in_all_messages_sent(s)    
        && inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)  
        && inv_g_d_a(s)
        && inv_g_d_b(s)   
        && pred_rcvd_attestation_shares_is_in_all_messages_sent(s)          
    } 

    lemma lem_inv_sequence_attestation_duties_to_be_served_orderd(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires is_sequence_attestation_duties_to_be_served_orderd(s)
    ensures is_sequence_attestation_duties_to_be_served_orderd(s')
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                assert s'.sequence_attestation_duties_to_be_served == s.sequence_attestation_duties_to_be_served;
            
            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                assert s'.sequence_attestation_duties_to_be_served == s.sequence_attestation_duties_to_be_served;
        }
        assert s'.sequence_attestation_duties_to_be_served == s.sequence_attestation_duties_to_be_served;

    }


    lemma lem_inv_db_of_validity_predicate_contains_all_previous_decided_values(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')  
    requires lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_precond(s)
    ensures inv_db_of_validity_predicate_contains_all_previous_decided_values(s')
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3(s, event, s', s_node);
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3a(s, event, s', s_node, node);
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3c(s, event, s', s_node, node);
                lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper4(s, event, s', s_node, node);
                lem_concl_exists_honest_dvc_that_sent_att_share_for_submitted_att(s, event, s');
                lem_pred_data_of_att_share_is_decided_value(s, event, s');
                lem_inv_sequence_attestation_duties_to_be_served_orderd(s, event, s');

                assert is_sequence_attestation_duties_to_be_served_orderd(s');
                assert  inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(s', s_node);
                match nodeEvent
                {
                    case ServeAttstationDuty(attestation_duty) => 
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served - 1;
                        lem_ServeAttstationDuty2(s, event, s');
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_serve_attestation_duty(
                            s_node,
                            attestation_duty,
                            s'_node,
                            s', 
                            node,
                            s'.index_next_attestation_duty_to_be_served
                        );
                        assert inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(s', s'_node);    
                              

                
                    case AttConsensusDecided(id, decided_attestation_data) =>  
                        assert s.index_next_attestation_duty_to_be_served == s'.index_next_attestation_duty_to_be_served;    
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper5(s, event, s');                 
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_att_consensus_decided(
                            s_node,
                            id,
                            decided_attestation_data,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        ); 
                        assert inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(s', s'_node);                   
                   
                    case ReceivedAttestationShare(attestation_share) => 
                        lem_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                        assert s_node.attestation_consensus_engine_state.att_slashing_db_hist == s'_node.attestation_consensus_engine_state.att_slashing_db_hist;
                        assert inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(s', s'_node);
        

                    case ImportedNewBlock(block) => 
                        var s_node := add_block_to_bn(s_node, nodeEvent.block);
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_f_listen_for_new_imported_blocks(
                            s_node,
                            block,
                            s'_node,
                            s', 
                            node,
                            s.index_next_attestation_duty_to_be_served
                        );  
                        assert inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(s', s'_node);                       
                 
                    case ResendAttestationShares => 
                        assert s_node.attestation_consensus_engine_state.att_slashing_db_hist == s'_node.attestation_consensus_engine_state.att_slashing_db_hist;
                        assert inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(s', s'_node);
                   
                    case NoEvent => 
                        assert s_node.attestation_consensus_engine_state.att_slashing_db_hist == s'_node.attestation_consensus_engine_state.att_slashing_db_hist;
                        assert inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(s', s'_node);                    

                }
                assert inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(s', s'_node);
                

                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(s', s'.honest_nodes_states[hn]); 
                {
                    if hn != node 
                    {
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3(s, event, s', s.honest_nodes_states[hn]);
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        assert inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(s', s'.honest_nodes_states[hn]);                        
                    }
                }     
                assert inv_db_of_validity_predicate_contains_all_previous_decided_values(s');          

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                forall hn |
                    && hn in s'.honest_nodes_states.Keys   
                ensures inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(s', s'.honest_nodes_states[hn]); 
                {
                    if hn != node 
                    {
                        lem_inv_db_of_validity_predicate_contains_all_previous_decided_values_helper3(s, event, s', s.honest_nodes_states[hn]);
                        assert s.honest_nodes_states[hn] == s'.honest_nodes_states[hn];
                        assert inv_db_of_validity_predicate_contains_all_previous_decided_values_body_body(s', s'.honest_nodes_states[hn]);                        
                    }
                }                
                assert inv_db_of_validity_predicate_contains_all_previous_decided_values(s');  

        }
    } 

}