include "../commons.dfy"
include "../att_spec_proofs/helper_sets_lemmas.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/dvn_next_invs_1_7.dfy"
include "../att_spec_proofs/dvn_next_invs_8_18.dfy"

module Att_Ind_Inv_With_Empty_Initial_Attestation_Slashing_DB
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV    
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Helper_Sets_Lemmas
    import opened DVN_Next_Invs_1_7
    import opened DVN_Next_Invs_8_18

    lemma ConsensusSpec_Init_implies_inv41<D(!new, 0)>(dvn: DVState, ci: ConsensusInstance<D>)
    requires ConsensusSpec.Init(ci, dvn.all_nodes, dvn.honest_nodes_states.Keys)
    ensures inv41(ci)
    { } 

    lemma NextConsensusDecides_implies_inv41<D(!new, 0)>(
            s: ConsensusInstance,
            honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,        
            s': ConsensusInstance
        )
    requires inv41(s) && isConditionForSafetyTrue(s)
    requires ConsensusSpec.NextConsensusDecides(s, honest_nodes_validity_predicates, s')
    ensures inv41(s')
    { } 

    lemma ConsensusSpec_Next_implies_inv41<D(!new, 0)>(
            s: ConsensusInstance,
            honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,        
            s': ConsensusInstance,
            output: Optional<OutCommand>
        )
    requires inv41(s) && isConditionForSafetyTrue(s)
    requires ConsensusSpec.Next(s, honest_nodes_validity_predicates, s', output)
    ensures inv41(s')
    { 
        assert NextConsensusDecides(s, honest_nodes_validity_predicates, s');
        NextConsensusDecides_implies_inv41(s, honest_nodes_validity_predicates, s');
        assert inv41(s');
        assert NextNodeStep(s', honest_nodes_validity_predicates, output);
        assert inv41(s');
    }

    lemma lemma_pred_4_1_b_helper(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    // requires NextEvent(s, event, s')
    requires pred_4_1_b(s)
    requires s'.all_nodes == s.all_nodes;
    requires s'.honest_nodes_states.Keys == s.honest_nodes_states.Keys;
    requires forall n | n in s'.honest_nodes_states.Keys :: s.honest_nodes_states[n].bn.attestations_submitted == s'.honest_nodes_states[n].bn.attestations_submitted;
    requires s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;    
    ensures pred_4_1_b(s');
    {
            forall hn, a |
                && hn in s.honest_nodes_states.Keys 
                && a in s.honest_nodes_states[hn].bn.attestations_submitted
            ensures exists hn', att_share: AttestationShare :: pred_4_1_b_exists(s', hn', att_share, a);
            {
                var hn', att_share: AttestationShare :|
                    pred_4_1_b_exists(s, hn', att_share, a);
                
                assert pred_4_1_b_exists(s', hn', att_share, a);
                assert exists hn', att_share: AttestationShare :: pred_4_1_b_exists(s', hn', att_share, a);
            }
            assert pred_4_1_b(s');
    }

    // lemma lemma_pred_4_1_b_f_start_next_duty()
    // ensures  
    //         forall
    //             s: DVCNodeState,
    //             attestation_duty: AttestationDuty,
    //             s': DVCNodeState
    //         |
    //             && f_start_next_duty.requires(s, attestation_duty)
    //             && s' == f_start_next_duty(s, attestation_duty).state
    //         ::
    //             s'.bn.attestations_submitted == s.bn.attestations_submitted
    // {

    // }

    lemma lemma_f_serve_attestation_duty_constants(
        s: DVCNodeState,
        attestation_duty: AttestationDuty,
        s': DVCNodeState
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
        lemma_f_check_for_next_queued_duty_constants(s_mod, s');
    }

    lemma lemma_f_check_for_next_queued_duty_constants(
        s: DVCNodeState,
        s': DVCNodeState
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
                    lemma_f_check_for_next_queued_duty_constants(s_mod, s');
                }
                else
                {
                    // var new_process := s.(
                    //     attestation_duties_queue := s.attestation_duties_queue[1..]
                    // );         
                    // lemma_pred_4_1_b_f_start_next_duty();
                }

        }
    }

    lemma lemma_f_att_consensus_decided_constants(
        s: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCNodeState
    )
    requires f_att_consensus_decided.requires(s, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(s, id, decided_attestation_data).state
    ensures s'.bn.attestations_submitted == s.bn.attestations_submitted
    ensures s'.rcvd_attestation_shares == s.rcvd_attestation_shares
    decreases s.attestation_duties_queue   
    {
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

        lemma_f_check_for_next_queued_duty_constants(s, s');             
    } 

    // Note: Lemma's name should be revisited due to second postcondition
    lemma lemma_f_listen_for_new_imported_blocks_constants(
        s: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState
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
            lemma_f_check_for_next_queued_duty_constants(s, s');
        }
    }  

    lemma lemma_f_listen_for_attestation_shares_constants(
        s: DVCNodeState,
        attestation_share: AttestationShare,
        s': DVCNodeState
    )
    requires f_listen_for_attestation_shares.requires(s, attestation_share)
    requires s' == f_listen_for_attestation_shares(s, attestation_share).state    
    ensures s'.attestation_consensus_engine_state == s.attestation_consensus_engine_state
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

    lemma lemma_recover_bls_signature()
    ensures forall r, s1, s2 |
                && recover_bls_signature.requires(r, s1)
                && recover_bls_signature.requires(r, s2)
                && recover_bls_signature(r, s1) == recover_bls_signature(r, s2)
            ::
                s1 == s2
    {
        lemma_verify_bls_siganture();
    }
    

    lemma lemma_pred_4_1_b_f_listen_for_attestation_shares(
        process: DVCNodeState,
        attestation_share: AttestationShare,

        s': DVCNodeState,
        dvn: DVState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires s' == f_listen_for_attestation_shares(process, attestation_share).state
    requires construct_signed_attestation_signature_assumptions_helper(
        process.construct_signed_attestation_signature,
        process.dv_pubkey,
        dvn.all_nodes
    )
    requires inv1(dvn)
    requires attestation_share in dvn.att_network.allMessagesSent
    requires pred_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(dvn, process)
    requires forall a | a in process.bn.attestations_submitted :: exists hn', att_share: AttestationShare ::
    pred_4_1_b_exists(dvn, hn', att_share, a)

    ensures forall a | a in s'.bn.attestations_submitted :: exists hn', att_share: AttestationShare :: pred_4_1_b_exists(dvn, hn', att_share, a)
    // ensures s'.bn.attestations_submitted == s.bn.attestations_submitted     
    {
        var activate_att_consensus_intances := process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys;

        if 
            || (activate_att_consensus_intances == {} && !process.latest_attestation_duty.isPresent())
            || (activate_att_consensus_intances != {} && minSet(activate_att_consensus_intances) <= attestation_share.data.slot)
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
                        dvn.all_nodes                    
                    );

                    assert process.construct_signed_attestation_signature(att_shares).isPresent();

                    assert construct_signed_attestation_signature_assumptions_helper_reverse(
                        process.construct_signed_attestation_signature,
                        process.dv_pubkey,
                        dvn.all_nodes
                    );

                    var data: AttestationData :|
                        construct_signed_attestation_signature_assumptions_helper_reverse_helper(
                            process.construct_signed_attestation_signature,
                            process.dv_pubkey,
                            dvn.all_nodes,
                            att_shares,
                            data                
                        );

                    assert pred_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(dvn, process);
                    assert att_shares <= dvn.att_network.allMessagesSent;

                    var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(data.target.epoch));
                    var signing_root := compute_attestation_signing_root(data, fork_version);
 

                    var signers := 
                    set signer, att_share | 
                        && att_share in att_shares
                        && signer in dvn.all_nodes
                        && verify_bls_siganture(signing_root, att_share.signature, signer)
                    ::
                        signer;

                    assert signers <= dvn.all_nodes;

                    lemmaThereExistsAnHonestInQuorum(dvn.all_nodes, dvn.all_nodes - dvn.honest_nodes_states.Keys, signers);

                    var h_s :| h_s in dvn.honest_nodes_states.Keys && h_s in signers;
                    var h_s_att :| h_s_att in att_shares && verify_bls_siganture(signing_root, h_s_att.signature, h_s);

                    // var attestation_signing_root := compute_attestation_signing_root(data, fork_version);

                    // assert signing_root == attestation_signing_root;                    

                    assert 
                    && h_s in dvn.honest_nodes_states.Keys
                    && h_s_att in dvn.att_network.allMessagesSent
                    && h_s_att.data == data
                    && verify_bls_siganture(signing_root, h_s_att.signature, h_s);

                    assert 
                    && h_s in dvn.honest_nodes_states.Keys
                    && h_s_att in dvn.att_network.allMessagesSent
                    && h_s_att.data == data
                    // && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(data.target.epoch));
                    && verify_bls_siganture(signing_root, h_s_att.signature, h_s);

                    // assert pred_attestations_signature_by_honest_node_implies_existence_of_attestation_with_correct_data_helper(
                    //     dvn,
                    //     h_s_att,
                    //     h_s,
                    //     signing_root
                    // );

                    // var att_share' :| pred_attestations_signature_by_honest_node_implies_existence_of_attestation_with_correct_data_helper_helper(dvn, att_share', signing_root, h_s_att.signature);

                    

                    // assert verify_bls_siganture(attestation_signing_root, h_s_att.signature, h_s);

                    assert pred_4_1_b_exists(
                        dvn,
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
                        assert exists hn', att_share: AttestationShare :: pred_4_1_b_exists(dvn, hn', att_share, a);
                    }
                    assert s' == state;
                }
            }   
    }


    lemma lemma_pred_rcvd_attestation_shares_is_in_all_messages_sent_f_listen_for_attestation_shares(
        process: DVCNodeState,
        attestation_share: AttestationShare,

        s': DVCNodeState,
        dvn: DVState
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires s' == f_listen_for_attestation_shares(process, attestation_share).state
    requires pred_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(dvn, process)
    requires attestation_share in dvn.att_network.allMessagesSent
    ensures pred_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(dvn, s') 
    {
        var activate_att_consensus_intances := process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys;

        if 
            || (activate_att_consensus_intances == {} && !process.latest_attestation_duty.isPresent())
            || (activate_att_consensus_intances != {} && minSet(activate_att_consensus_intances) <= attestation_share.data.slot)
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

                    assert pred_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(dvn, s');

                    assert s' == state;
                }
            }   
    }    


    lemma lemma_pred_4_1_b(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEvent(s, event, s')
    requires pred_4_1_b(s)
    requires construct_signed_attestation_signature_assumptions_helper(
        s.construct_signed_attestation_signature,
        s.dv_pubkey,
        s.all_nodes
    )
    requires inv3(s)  
    requires invNetwork(s)
    requires inv1(s)
    requires pred_rcvd_attestation_shares_is_in_all_messages_sent(s)    
    ensures pred_4_1_b(s')
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
                        // // Proved
                        forall n | n in s'.honest_nodes_states.Keys
                        ensures s.honest_nodes_states[n].bn.attestations_submitted == s'.honest_nodes_states[n].bn.attestations_submitted;
                        {
                            if n != node 
                            {
                                assert s.honest_nodes_states[n].bn.attestations_submitted == s'.honest_nodes_states[n].bn.attestations_submitted;
                            }
                            else 
                            {
                                lemma_f_serve_attestation_duty_constants(s.honest_nodes_states[node], attestation_duty, s'.honest_nodes_states[node]);
                            }
                        }
                        lemma_pred_4_1_b_helper(s, event, s');
                        assert pred_4_1_b(s');                    
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        // Proved
                        lemma_f_att_consensus_decided_constants(s.honest_nodes_states[node], id, decided_attestation_data, s'.honest_nodes_states[node]);
                        lemma_pred_4_1_b_helper(s, event, s');
                        assert pred_4_1_b(s');                    
                    case ReceviedAttesttionShare(attestation_share) => 
                        assert multiset(addReceipientToMessages<AttestationShare>({attestation_share}, node)) <= s.att_network.messagesInTransit;

                        assert MessaageWithRecipient(message := attestation_share, receipient := node) in s.att_network.messagesInTransit;        

                        
                        assert attestation_share in s.att_network.allMessagesSent;

                        forall hn | hn in s.honest_nodes_states.Keys
                        ensures forall a | 
                                         a in s'.honest_nodes_states[hn].bn.attestations_submitted
                                ::
                                 exists hn', att_share: AttestationShare :: pred_4_1_b_exists(s', hn', att_share, a);            
                        {
                            if hn != node 
                            {
                                assert s'.honest_nodes_states[hn] == s.honest_nodes_states[hn];
                                forall a | 
                                         a in s'.honest_nodes_states[hn].bn.attestations_submitted
                                ensures exists hn', att_share: AttestationShare :: pred_4_1_b_exists(s', hn', att_share, a);            
                                {
                                    assert a in s.honest_nodes_states[hn].bn.attestations_submitted;
                                    var hn', att_share: AttestationShare :| pred_4_1_b_exists(s, hn', att_share, a);                                    
                                    
                                    assert pred_4_1_b_exists(s', hn', att_share, a);

                                    assert exists hn', att_share: AttestationShare :: pred_4_1_b_exists(s', hn', att_share, a);                                    
                                }
                            }
                            else 
                            {
                                lemma_pred_4_1_b_f_listen_for_attestation_shares(
                                    s_node,
                                    attestation_share,
                                    s'_node,
                                    s
                                );

                                forall a | 
                                         a in s'.honest_nodes_states[hn].bn.attestations_submitted
                                ensures exists hn', att_share: AttestationShare :: pred_4_1_b_exists(s', hn', att_share, a);            
                                {
                                    // assert a in s.honest_nodes_states[hn].bn.attestations_submitted;
                                    var hn', att_share: AttestationShare :| pred_4_1_b_exists(s, hn', att_share, a);                                    
                                    
                                    assert pred_4_1_b_exists(s', hn', att_share, a);

                                    assert exists hn', att_share: AttestationShare :: pred_4_1_b_exists(s', hn', att_share, a);                                    
                                }                                

                                // assert forall a | a in s'_node.bn.attestations_submitted :: exists hn', att_share: AttestationShare, fork_version :: pred_4_1_b_exists(s', hn', att_share, fork_version, a);                                
                            }
                        }

                        assert pred_4_1_b(s');         

                    case ImportedNewBlock(block) => 
                        // Provded
                        var s_node := add_block_to_bn(s_node, nodeEvent.block);
                        lemma_f_listen_for_new_imported_blocks_constants(s_node, block, s'_node);
                        lemma_pred_4_1_b_helper(s, event, s');
                        assert pred_4_1_b(s');                    
                    case ResendAttestationShares => 
                        // Proved
                        lemma_pred_4_1_b_helper(s, event, s');
                        assert pred_4_1_b(s');                    
                    case NoEvent => 
                        // Proved
                        lemma_pred_4_1_b_helper(s, event, s');
                        assert pred_4_1_b(s');
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                lemma_pred_4_1_b_helper(s, event, s');
                assert pred_4_1_b(s');
        }
    }    

    lemma lemma_pred_rcvd_attestation_shares_is_in_all_messages_sent(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
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
                        lemma_f_serve_attestation_duty_constants(s_node, attestation_duty, s'_node);
                        assert pred_rcvd_attestation_shares_is_in_all_messages_sent(s');                    
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_f_att_consensus_decided_constants(s_node, id, decided_attestation_data, s'_node);
                        assert pred_rcvd_attestation_shares_is_in_all_messages_sent(s');                    
                    case ReceviedAttesttionShare(attestation_share) => 
                        assert multiset(addReceipientToMessages<AttestationShare>({attestation_share}, node)) <= s.att_network.messagesInTransit;

                        assert MessaageWithRecipient(message := attestation_share, receipient := node) in s.att_network.messagesInTransit;        

                        
                        assert attestation_share in s.att_network.allMessagesSent;                    
                        lemma_pred_rcvd_attestation_shares_is_in_all_messages_sent_f_listen_for_attestation_shares(
                            s_node,
                            attestation_share,
                            s'_node,
                            s
                        );
                        assert pred_rcvd_attestation_shares_is_in_all_messages_sent(s');
                    case ImportedNewBlock(block) => 
                        var s_node := add_block_to_bn(s_node, nodeEvent.block);
                        lemma_f_listen_for_new_imported_blocks_constants(s_node, block, s'_node);
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

    // lemma lemma_getMessagesFromMessagesWithRecipient<M>(mswr: set<MessaageWithRecipient<M>>, message: M)
    // requires forall m | m in mswr :: m.message == message;   
    // {
    //     var r := getMessagesFromMessagesWithRecipient(mswr);
    //     assert forall e | e in r :: e == message;
    //     if r != {message}
    //     {
    //         if r == {}
    //         {
                
    //         }
    //     }
    // } 


    lemma lemma_pred_4_1_c_helper(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEvent(s, event, s')
    requires pred_4_1_c(s)
    requires pred_4_1_f_b(s)
    requires inv1(s)
    requires inv53(s)
    requires inv3(s)
    requires |s.all_nodes| > 0
    requires s'.att_network.allMessagesSent == s.att_network.allMessagesSent + 
                            getMessagesFromMessagesWithRecipient({});
    ensures  pred_4_1_c(s');
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
        assert pred_4_1_c(s');        
    }     

    // Ver time: 1m 17s
    lemma lemma_pred_4_1_c_att_consensus_decided(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEvent(s, event, s')
    requires event.HonestNodeTakingStep?
    requires event.event.AttConsensusDecided?
    requires pred_4_1_c(s)
    requires pred_4_1_f_b(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)  
    requires inv1(s)
    requires inv2(s)
    requires inv53(s)
    requires inv3(s)
    requires pred_4_1_f_a(s)    
    requires pred_4_1_g_i(s)
    requires pred_4_1_g_i_for_dvc(s)          
    requires |s.all_nodes| > 0
    ensures pred_4_1_c(s')   
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                match nodeEvent
                {
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        assert pred_4_1_c(s') by 
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
                            assert getMessagesFromMessagesWithRecipient(messagesToBeSent) ==  {attestation_with_signature_share};
                            assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent + 
                                {attestation_with_signature_share}; 

                            assert pred_4_1_c(s') by 
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
                                    var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));
                                    if att_share in s.att_network.allMessagesSent
                                    {
                                        assert s.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent();
                                        assert s.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;   
                                    }
                                    else
                                    {
                                        assert att_share == attestation_with_signature_share;
                                        assert id in s.consensus_on_attestation_data.Keys ;

                                        var validityPredicates :| ConsensusSpec.Next(
                                            s.consensus_on_attestation_data[id],
                                            validityPredicates,
                                            s'.consensus_on_attestation_data[id],
                                            Some(Decided(node, decided_attestation_data))
                                        );                             


                                        assert s'.consensus_on_attestation_data[id].decided_value.isPresent();
                                        lemma_pred_4_1_f_b(s, event, s');
                                        assert s'.consensus_on_attestation_data[id].decided_value.safe_get().slot == id;                                     
                                        assert s'.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;                                     
                                    }
                                }
                            }

                            assert pred_4_1_c(s');
                        }    
                }
        }
    }

    lemma lemma_pred_4_1_c_att_adversary(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEvent(s, event, s')
    requires event.AdeversaryTakingStep?
    requires pred_4_1_c(s)
    requires pred_4_1_f_b(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)  
    requires inv1(s)
    requires inv53(s)
    requires inv3(s)
    requires |s.all_nodes| > 0
    ensures pred_4_1_c(s') 
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
    
        assert pred_4_1_c(s');
    }      

    // Ver time: 1m 35s
    lemma lemma_pred_4_1_c(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEvent(s, event, s')
    requires pred_4_1_c(s)
    requires pred_4_1_f_b(s)
    requires inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(s)  
    requires inv1(s)
    requires inv2(s)
    requires inv53(s)
    requires inv3(s)
    requires pred_4_1_f_a(s)    
    requires pred_4_1_g_i(s)    
    requires pred_4_1_g_i_for_dvc(s)          
    requires |s.all_nodes| > 0
    ensures pred_4_1_c(s')   
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];
                if nodeEvent.AttConsensusDecided? 
                {
                    lemma_pred_4_1_c_att_consensus_decided(s, event, s');
                }
                else 
                {
                    match nodeEvent
                    {
                        case ServeAttstationDuty(attestation_duty) => 
                            var messagesToBeSent := f_serve_attestation_duty(s_node, attestation_duty).outputs.att_shares_sent;
                            assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent + 
                                getMessagesFromMessagesWithRecipient(messagesToBeSent);
                            lemma_f_serve_attestation_duty_constants(s_node, attestation_duty, s'_node);
                            assert messagesToBeSent == {};
                            assert s'.att_network.allMessagesSent == s.att_network.allMessagesSent;
                            
                                                                    
                        case ReceviedAttesttionShare(attestation_share) => 
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
                            lemma_f_listen_for_new_imported_blocks_constants(s_node, block, s'_node);
                            assert messagesToBeSent == {};
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
                    lemma_pred_4_1_c_helper(s, event, s');
                }


            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                lemma_pred_4_1_c_att_adversary(s, event, s');

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
    lemma lemma_pred_4_1_f_a_helper(
        s: DVState,
        event: DV.Event,
        cid: Slot,
        s': DVState
    )
    requires NextEvent(s, event, s')
    requires event.HonestNodeTakingStep?
    requires cid in s'.consensus_on_attestation_data.Keys
    requires inv1(s)
    requires inv53(s)
    requires inv3(s)
    requires pred_4_1_f_a(s)    
    requires s.consensus_on_attestation_data[cid].decided_value.isPresent()
    ensures is_a_valid_decided_value(s'.consensus_on_attestation_data[cid]); 
    // ensures pred_4_1_f_a(s')   
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
                            && cid in s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.attestation_consensus_active_instances.Keys
                        ::
                            s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.attestation_consensus_active_instances[cid].validityPredicate
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

    lemma lemma_pred_4_1_f_a(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEvent(s, event, s')
    requires inv1(s)
    requires inv53(s)
    requires inv3(s)
    requires pred_4_1_f_a(s)    
    ensures pred_4_1_f_a(s')   
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
                        lemma_pred_4_1_f_a_helper(s, event, cid, s');
                    }
                    else
                    {
                        assert is_a_valid_decided_value(s'.consensus_on_attestation_data[cid]);
                    }
                }
                assert pred_4_1_f_a(s');
               

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                assert pred_4_1_f_a(s');
        }        
    } 

    lemma lemma_pred_4_1_f_b_helper(
        s: DVState,
        cid: Slot
    )
    requires pred_4_1_f_a(s)    
    requires pred_4_1_g_i(s)
    requires inv1(s)
    requires inv2(s)
    requires inv3(s)
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
                pred_4_1_g_i_body(cid, attestation_duty, attestation_slashing_db, vp);

        assert s_consensus.decided_value.safe_get().slot == cid;
    }

    lemma lemma_pred_4_1_f_b(
        s: DVState,
        event: DV.Event,
        s': DVState
    )
    requires NextEvent(s, event, s')
    requires pred_4_1_f_a(s)    
    requires pred_4_1_g_i(s)
    requires pred_4_1_g_i_for_dvc(s)  
    requires inv1(s)
    requires inv2(s)
    requires inv3(s)  
    ensures pred_4_1_f_b(s') 
    {
        lemma_inv1_dvn_next(s, event, s');
        lemma_inv2_dvn_next(s, event, s');
        lemma_inv3_dvn_next(s, event, s');
        lemma_pred_4_1_f_a(s, event, s');
        lemma_pred_4_1_f_g_i(s, event, s');
        lemma_pred_4_1_f_b2(s');   
    }     

    lemma lemma_pred_4_1_f_b2(
        s: DVState
    )
    requires pred_4_1_f_a(s)    
    requires pred_4_1_g_i(s)
    requires inv1(s)
    requires inv2(s)
    requires inv3(s)
    ensures pred_4_1_f_b(s) 
    {
        forall cid |
            && cid in s.consensus_on_attestation_data.Keys
            && s.consensus_on_attestation_data[cid].decided_value.isPresent()
        {
           lemma_pred_4_1_f_b_helper(s, cid);
        }        
    }        

     

    lemma lemma_pred_4_1_f_g_i_get_s_w_honest_node_states_updated(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Types.Event
    ) returns (s_w_honest_node_states_updated: DVState)
    requires node in s.honest_nodes_states
    ensures s_w_honest_node_states_updated ==
                if nodeEvent.ImportedNewBlock? then 
                    s.(
                        honest_nodes_states := s.honest_nodes_states[node := add_block_to_bn(s.honest_nodes_states[node], nodeEvent.block)]
                    )
                else 
                    s 
                ;  
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

    lemma lemma_pred_4_1_f_g_i_helper(
        s: DVState,
        event: DV.Event,
        s': DVState,
        cid: Slot,
        hn: BLSPubkey,
        vp: AttestationData -> bool
    )   returns (attestation_duty: AttestationDuty, attestation_slashing_db: set<SlashingDBAttestation>)
    requires NextEvent(s, event, s') 
    requires inv1(s)
    requires inv2(s)
    requires inv3(s)      
    requires
            && hn in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions.Keys
            && vp in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions[hn]
    requires event.HonestNodeTakingStep?
    requires pred_4_1_g_i(s)
    requires pred_4_1_g_i_for_dvc(s)
    ensures pred_4_1_g_i_body(cid, attestation_duty, attestation_slashing_db, vp); 
    {
        assert s.att_network.allMessagesSent <= s'.att_network.allMessagesSent;
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var s_node := s.honest_nodes_states[node];
                var s'_node := s'.honest_nodes_states[node];

                var s_w_honest_node_states_updated :=
                    lemma_pred_4_1_f_g_i_get_s_w_honest_node_states_updated(s, node, nodeEvent);         

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
                            && cid in s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.attestation_consensus_active_instances.Keys
                        ::
                            s_w_honest_node_states_updated.honest_nodes_states[n].attestation_consensus_engine_state.attestation_consensus_active_instances[cid].validityPredicate
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

                attestation_duty, attestation_slashing_db :| pred_4_1_g_i_body(cid, attestation_duty, attestation_slashing_db, vp);

            }
            else 
            {
                assert vp in validityPredicates.Values;
                var vpn :| vpn in validityPredicates.Keys && validityPredicates[vpn] == vp;
                assert validityPredicates[vpn] == s_w_honest_node_states_updated.honest_nodes_states[vpn].attestation_consensus_engine_state.attestation_consensus_active_instances[cid].validityPredicate;

                assert vpn in s.honest_nodes_states.Keys;
                assert cid in s_w_honest_node_states_updated.honest_nodes_states[vpn].attestation_consensus_engine_state.attestation_consensus_active_instances.Keys;

                assert s_w_honest_node_states_updated.honest_nodes_states[vpn].attestation_consensus_engine_state == s.honest_nodes_states[vpn].attestation_consensus_engine_state;
                assert pred_4_1_g_i_for_dvc_single_dvc(s, vpn, cid);

                attestation_duty, attestation_slashing_db :| pred_4_1_g_i_body(cid, attestation_duty, attestation_slashing_db, vp);
            }

            assert pred_4_1_g_i_body(cid, attestation_duty, attestation_slashing_db, vp);


        }

    }  

    lemma lemma_pred_4_1_f_g_i(
        s: DVState,
        event: DV.Event,
        s': DVState
    )   
    requires NextEvent(s, event, s') 
    requires pred_4_1_g_i(s)
    requires inv1(s)
    requires inv2(s)
    requires inv3(s)      
    requires pred_4_1_g_i_for_dvc(s)  
    ensures pred_4_1_g_i(s')   
    {
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                forall hn, cid: nat, vp |
                    && hn in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions.Keys
                    && vp in s'.consensus_on_attestation_data[cid].honest_nodes_validity_functions[hn]
                ensures exists attestation_duty, attestation_slashing_db :: pred_4_1_g_i_body(cid, attestation_duty, attestation_slashing_db, vp)
                {
                    var attestation_duty: AttestationDuty, attestation_slashing_db := lemma_pred_4_1_f_g_i_helper(s, event, s', cid, hn, vp);
                }
                assert pred_4_1_g_i(s');

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                assert pred_4_1_g_i(s');
        }
    }   

    lemma lemma_pred_4_1_f_g_for_dvc_updateConsensusInstanceValidityCheckHelper(
        m: map<Slot, AttestationConsensusValidityCheckState>,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        m': map<Slot, AttestationConsensusValidityCheckState>
    )    
    requires m' == updateConsensusInstanceValidityCheckHelper(m, new_attestation_slashing_db)
    requires forall k | k in m :: pred_4_1_g_i_for_dvc_single_dvc_2_body_body(k, m[k].attestation_duty, m[k].validityPredicate)
    ensures forall k | k in m' :: pred_4_1_g_i_for_dvc_single_dvc_2_body_body(k, m'[k].attestation_duty, m'[k].validityPredicate)    
    {
        forall k | k in  m 
        ensures k in m'
        {
            lemmaMapKeysHasOneEntryInItems(m, k);
            assert k in m';
        }

        assert m.Keys == m'.Keys;

        forall k | k in m' 
        ensures pred_4_1_g_i_body(k, m'[k].attestation_duty, new_attestation_slashing_db, m'[k].validityPredicate); 
        {
            assert m'[k] == m[k].(
                    validityPredicate := (ad: AttestationData) => consensus_is_valid_attestation_data(new_attestation_slashing_db, ad, m[k].attestation_duty)
            );
            assert  pred_4_1_g_i_body(k, m'[k].attestation_duty, new_attestation_slashing_db, m'[k].validityPredicate);        
        }
    }

    lemma lemma_pred_4_1_f_g_for_dvc_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        s': DVCNodeState
    )
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires s' == f_serve_attestation_duty(process, attestation_duty).state  
    requires pred_4_1_g_i_for_dvc_single_dvc_2(process) 
    ensures pred_4_1_g_i_for_dvc_single_dvc_2(s'); 
    {
        var s_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );
        assert pred_4_1_g_i_for_dvc_single_dvc_2(s_mod); 
        lemma_pred_4_1_f_g_for_dvc_f_check_for_next_queued_duty(s_mod, s');        
    }    

    lemma lemma_pred_4_1_f_g_for_dvc_f_check_for_next_queued_duty(
        process: DVCNodeState,
        s': DVCNodeState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires s' == f_check_for_next_queued_duty(process).state   
    requires pred_4_1_g_i_for_dvc_single_dvc_2(process) 
    ensures pred_4_1_g_i_for_dvc_single_dvc_2(s'); 
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

                lemma_pred_4_1_f_g_for_dvc_updateConsensusInstanceValidityCheckHelper(
                        process.attestation_consensus_engine_state.attestation_consensus_active_instances,
                        new_attestation_slashing_db,
                        s_mod.attestation_consensus_engine_state.attestation_consensus_active_instances
                );

                lemma_pred_4_1_f_g_for_dvc_f_check_for_next_queued_duty(s_mod, s');

            }
            else 
            {
                var attestation_duty := process.attestation_duties_queue[0];
                var attestation_slashing_db := process.attestation_slashing_db;

                var acvc := AttestationConsensusValidityCheckState(
                    attestation_duty := attestation_duty,
                    validityPredicate := (ad: AttestationData) => consensus_is_valid_attestation_data(attestation_slashing_db, ad, attestation_duty)
                );     

                assert s'.attestation_consensus_engine_state.attestation_consensus_active_instances == process.attestation_consensus_engine_state.attestation_consensus_active_instances[attestation_duty.slot := acvc];

                forall cid | 
                    && cid in s'.attestation_consensus_engine_state.attestation_consensus_active_instances  
                ensures pred_4_1_g_i_for_dvc_single_dvc_2_body(s', cid); 
                {
                    if cid != attestation_duty.slot 
                    {
                        assert cid in process.attestation_consensus_engine_state.attestation_consensus_active_instances;
                        assert pred_4_1_g_i_for_dvc_single_dvc_2_body(s', cid); 
                    }
                    else 
                    {
                        assert pred_4_1_g_i_body(
                            cid,
                            attestation_duty,
                            attestation_slashing_db,
                            acvc.validityPredicate
                        );
                        assert pred_4_1_g_i_for_dvc_single_dvc_2_body(s', cid); 
                    }
                }              

                assert pred_4_1_g_i_for_dvc_single_dvc_2(s'); 
            }
        } 
        else 
        {
            assert pred_4_1_g_i_for_dvc_single_dvc_2(s'); 
        }       
    }

    lemma lemma_pred_4_1_f_g_for_dvc_f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData,        
        s': DVCNodeState
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires s' == f_att_consensus_decided(process, id, decided_attestation_data).state
    requires pred_4_1_g_i_for_dvc_single_dvc_2(process) 
    ensures pred_4_1_g_i_for_dvc_single_dvc_2(s'); 
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

        lemma_pred_4_1_f_g_for_dvc_updateConsensusInstanceValidityCheckHelper(
                process.attestation_consensus_engine_state.attestation_consensus_active_instances,
                attestation_slashing_db,
                s_mod.attestation_consensus_engine_state.attestation_consensus_active_instances
        );            

        lemma_pred_4_1_f_g_for_dvc_f_check_for_next_queued_duty(s_mod, s');             
    }     

    lemma lemma_pred_4_1_f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state
    requires pred_4_1_g_i_for_dvc_single_dvc_2(process) 
    ensures pred_4_1_g_i_for_dvc_single_dvc_2(s');     
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

            lemma_pred_4_1_f_g_for_dvc_updateConsensusInstanceValidityCheckHelper(
                    process.attestation_consensus_engine_state.attestation_consensus_active_instances,
                    new_attestation_slashing_db,
                    s_mod.attestation_consensus_engine_state.attestation_consensus_active_instances
            ); 

            lemma_pred_4_1_f_g_for_dvc_f_check_for_next_queued_duty(s_mod, s');             
           
        }
    }      

    lemma lemma_pred_4_1_f_g_for_dvc(
        s: DVState,
        event: DV.Event,
        s': DVState
    )   
    requires NextEvent(s, event, s') 
    requires inv1(s)
    requires inv2(s)
    requires inv3(s)      
    requires pred_4_1_g_i_for_dvc(s)  
    ensures pred_4_1_g_i_for_dvc(s')    
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
                        ensures pred_4_1_g_i_for_dvc_single_dvc_2(s'.honest_nodes_states[n]); 
                        {
                            if n == node
                            {
                                lemma_pred_4_1_f_g_for_dvc_f_serve_attestation_duty(s_node, attestation_duty, s'_node);
                                assert pred_4_1_g_i_for_dvc_single_dvc_2(s'_node); 
                            }
                        }
                        assert pred_4_1_g_i_for_dvc(s');                        
                  
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        forall n | n in s'.honest_nodes_states
                        ensures pred_4_1_g_i_for_dvc_single_dvc_2(s'.honest_nodes_states[n]); 
                        {
                            if n == node
                            {
                                lemma_pred_4_1_f_g_for_dvc_f_att_consensus_decided(s_node, id, decided_attestation_data, s'_node);
                                assert pred_4_1_g_i_for_dvc_single_dvc_2(s'_node); 
                            }
                        }
                        assert pred_4_1_g_i_for_dvc(s');                       
              
                    case ReceviedAttesttionShare(attestation_share) => 
                        forall n | n in s'.honest_nodes_states
                        ensures s'.honest_nodes_states[n].attestation_consensus_engine_state == s.honest_nodes_states[n].attestation_consensus_engine_state
                        {
                            if n == node
                            {
                                lemma_f_listen_for_attestation_shares_constants(s_node, attestation_share, s'_node);
                            }
                        }
                        assert pred_4_1_g_i_for_dvc(s');     

                    case ImportedNewBlock(block) => 
                        forall n | n in s'.honest_nodes_states
                        ensures pred_4_1_g_i_for_dvc_single_dvc_2(s'.honest_nodes_states[n]); 
                        {
                            if n == node
                            {
                                var s_node := add_block_to_bn(s_node, nodeEvent.block);
                                lemma_pred_4_1_f_listen_for_new_imported_blocks(s_node, block, s'_node);
                                assert pred_4_1_g_i_for_dvc_single_dvc_2(s'_node); 
                            }
                        }
                        assert pred_4_1_g_i_for_dvc(s');                        
               
                    case ResendAttestationShares => 
                        assert pred_4_1_g_i_for_dvc(s');
                   
                    case NoEvent => 
                        assert pred_4_1_g_i_for_dvc(s');
                }            


            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                assert pred_4_1_g_i_for_dvc(s');
        }        
    }    
}