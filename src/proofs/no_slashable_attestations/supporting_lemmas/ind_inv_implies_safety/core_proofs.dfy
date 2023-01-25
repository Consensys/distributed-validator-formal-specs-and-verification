include "../../../../common/commons.dfy"
include "../../common/attestation_creation_instrumented.dfy"
include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_attestation_creation.dfy"

include "../../../common/helper_sets_lemmas.dfy"

include "../dv_next_preserves_ind_inv/invs_fnc_1.dfy"
include "../dv_next_preserves_ind_inv/invs_fnc_2.dfy"
include "../dv_next_preserves_ind_inv/invs_dv_next_1.dfy"
include "../dv_next_preserves_ind_inv/invs_dv_next_2.dfy"
include "../dv_next_preserves_ind_inv/invs_dv_next_3.dfy"
include "../dv_next_preserves_ind_inv/invs_dv_next_4.dfy"
include "../dv_next_preserves_ind_inv/invs_dv_next_5.dfy"

include "../inv.dfy"

module Core_Proofs
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Invs_DV_Next_3
    import opened Helper_Sets_Lemmas
    import opened DVC_Spec_Axioms


    predicate is_slashable_attestation_data_eth_spec(data_1: AttestationData, data_2: AttestationData)
    {
        || (data_1 != data_2 && data_1.target.epoch == data_2.target.epoch)
        || (data_1.source.epoch < data_2.source.epoch && data_2.target.epoch < data_1.target.epoch)
    }

    lemma lem_is_slashable_attestation_data(
        att_slashing_db': set<SlashingDBAttestation>, 
        ad': AttestationData,
        sdba: SlashingDBAttestation,
        sdba': SlashingDBAttestation

    )
    requires !is_slashable_attestation_data(att_slashing_db', ad')
    requires sdba in att_slashing_db'
    requires sdba'.source_epoch == ad'.source.epoch 
    requires sdba'.target_epoch == ad'.target.epoch 
    ensures !is_slashable_attestation_pair(sdba, sdba')
    ensures !is_slashable_attestation_pair(sdba', sdba)
    {

    }

    lemma lem_no_slashable_submitted_attestations_with_different_slots_i(dv: DVState, a: Attestation, a': Attestation)
    requires |dv.all_nodes| > 0
    requires inv_quorum_constraints(dv)   
    requires inv_unchanged_paras_of_consensus_instances(dv)
    requires inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv)
    requires inv_data_of_att_share_is_decided_value(dv)
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(dv)    
    requires && a in dv.all_attestations_created
             && is_valid_attestation(a, dv.dv_pubkey)
    requires && a' in dv.all_attestations_created
             && is_valid_attestation(a', dv.dv_pubkey)
    requires a.data.slot < a'.data.slot 
    ensures && var consa := dv.consensus_on_attestation_data[a.data.slot];
            && var consa' := dv.consensus_on_attestation_data[a'.data.slot];   
            && exists m: BLSPubkey, h_nodes_a: set<BLSPubkey>, h_nodes_a': set<BLSPubkey> :: 
                        inv_exists_honest_node_that_contributed_to_decisions_of_consensus_instances(dv, a, a', m, consa, consa', h_nodes_a, h_nodes_a')    
    {
        var hna, att_share :|
                && is_honest_node(dv, hna)
                && att_share in dv.att_network.allMessagesSent
                && att_share.data == a.data
                && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));
                && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
                && verify_bls_siganture(attestation_signing_root, att_share.signature, hna);     

        var hna', att_share' :|
                && is_honest_node(dv, hna)
                && att_share' in dv.att_network.allMessagesSent
                && att_share'.data == a'.data
                && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share'.data.target.epoch));
                && var attestation_signing_root := compute_attestation_signing_root(att_share'.data, fork_version);
                && verify_bls_siganture(attestation_signing_root, att_share'.signature, hna');  

        assert
                && dv.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent()
                && dv.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;       

        assert
                && dv.consensus_on_attestation_data[att_share'.data.slot].decided_value.isPresent()
                && dv.consensus_on_attestation_data[att_share'.data.slot].decided_value.safe_get() == att_share'.data;   

        var consa := dv.consensus_on_attestation_data[a.data.slot];
        var consa' := dv.consensus_on_attestation_data[a'.data.slot];                    

        assert is_a_valid_decided_value(consa); 
        assert is_a_valid_decided_value(consa');  

        assert consa.decided_value.isPresent();

        var h_nodes_a :| is_a_valid_decided_value_according_to_set_of_nodes(consa, h_nodes_a);
        var h_nodes_a' :| is_a_valid_decided_value_according_to_set_of_nodes(consa', h_nodes_a');

        assert consa.all_nodes == consa'.all_nodes == dv.all_nodes;

        var nodes := consa.all_nodes;
        var honest_nodes := consa.honest_nodes_status.Keys;
        var byz_nodes := nodes - honest_nodes;
        
        assert h_nodes_a * byz_nodes == {};
        assert h_nodes_a' * byz_nodes == {};        
        assert |h_nodes_a + byz_nodes| >= quorum(|nodes|);
        assert |h_nodes_a' + byz_nodes| >= quorum(|nodes|);
        assert |byz_nodes| <= f(|nodes|);
        assert nodes != {};    

        lemmaQuorumIntersection(nodes, byz_nodes, h_nodes_a + byz_nodes, h_nodes_a' + byz_nodes);
            
        var m: BLSPubkey :| m in honest_nodes && m in h_nodes_a && m in h_nodes_a';  

        assert inv_exists_honest_node_that_contributed_to_decisions_of_consensus_instances(dv, a, a', m, consa, consa', h_nodes_a, h_nodes_a');
        assert ( exists m: BLSPubkey, h_nodes_a: set<BLSPubkey>, h_nodes_a': set<BLSPubkey> :: 
                                inv_exists_honest_node_that_contributed_to_decisions_of_consensus_instances(dv, a, a', m, consa, consa', h_nodes_a, h_nodes_a') ); 
    }

        // Wrong: 1st try in a new version
//     lemma lem_no_slashable_submitted_attestations_with_different_slots_ii(
//                 dv: DVState, 
//                 a: Attestation, 
//                 a': Attestation
//     )
//     requires inv_quorum_constraints(dv)    
//     requires inv_exists_honest_node_that_contributed_to_creation_of_submitted_attestations_body(dv, a, a')
//     requires inv_if_honest_node_sends_att_share_it_receives_att_data_before(dv)
//     ensures && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
//             && !is_slashable_attestation_data_eth_spec(a'.data, a.data)
//     {    
//         var hn: BLSPubkey, att_shares: set<AttestationShare>, att_shares': set<AttestationShare> :|
//                 && is_honest_node(dv, hn)
//                 && pred_attestation_is_created_based_on_sent_attestation_shares(dv, a, att_shares)
//                 && pred_is_owner_of_one_attestaion_share_in_set_of_shares(dv.honest_nodes_states[hn], att_shares)
//                 && pred_attestation_is_created_based_on_sent_attestation_shares(dv, a', att_shares')
//                 && pred_is_owner_of_one_attestaion_share_in_set_of_shares(dv.honest_nodes_states[hn], att_shares')
//                 ;
//         var dvc: DVCState := dv.honest_nodes_states[hn];
//         var att_share: AttestationShare :| 
//                 && att_share in att_shares 
//                 && pred_verify_owner_of_attestation_share_with_bls_signature(dvc, att_share)
//                 ;
//         var att_share': AttestationShare :| 
//                 && att_share' in att_shares' 
//                 && pred_verify_owner_of_attestation_share_with_bls_signature(dvc, att_share')
//                 ;

//         assert inv_if_honest_node_sends_att_share_it_receives_att_data_before_body(dvc, att_share);
//         assert inv_if_honest_node_sends_att_share_it_receives_att_data_before_body(dvc, att_share');

//         var att_data: AttestationData := att_share.data;
//         var slot: Slot := att_data.slot;
//         var att_duty: AttestationDuty, vp: AttestationData -> bool :|
//                 && att_duty in dvc.all_rcvd_duties
//                 && slot in dvc.attestation_consensus_engine_state.att_slashing_db_hist.Keys
//                 && vp in dvc.attestation_consensus_engine_state.att_slashing_db_hist[slot].Keys
//                 // && consensus_is_valid_attestation_data(dvc.attestation_slashing_db, att_data, att_duty)
//                 && vp(att_data)
//                 ;

//         assert consensus_is_valid_attestation_data(dvc.attestation_slashing_db, att_data, att_duty);

//         var att_data': AttestationData := att_share'.data;
//         var slot': Slot := att_data'.slot;
//         var att_duty': AttestationDuty, vp': AttestationData -> bool :|
//                 && att_duty' in dvc.all_rcvd_duties
//                 && slot' in dvc.attestation_consensus_engine_state.att_slashing_db_hist.Keys
//                 && vp' in dvc.attestation_consensus_engine_state.att_slashing_db_hist[slot'].Keys
//                 // && consensus_is_valid_attestation_data(dvc.attestation_slashing_db, att_data', att_duty')
//                 && vp'(att_data')
//                 ;

//         // assert  && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
//         //         && !is_slashable_attestation_data_eth_spec(a'.data, a.data)
//         //         ;
//     }

        // Wrong: proof in the old version
    lemma lem_no_slashable_submitted_attestations_with_different_slots_ii(
                dv: DVState, 
                a: Attestation, 
                a': Attestation, 
                m: BLSPubkey, 
                consa: ConsensusInstance<AttestationData>, consa': ConsensusInstance<AttestationData>,
                h_nodes_a: set<BLSPubkey>, h_nodes_a': set<BLSPubkey>)
    requires |dv.all_nodes| > 0
    requires inv_quorum_constraints(dv)    
    requires inv_exists_honest_node_that_contributed_to_decisions_of_consensus_instances(dv, a, a', m, consa, consa', h_nodes_a, h_nodes_a')
    requires && consa.decided_value.isPresent()
             && consa'.decided_value.isPresent()
             && a.data == consa.decided_value.safe_get()
             && a'.data == consa'.decided_value.safe_get()
    requires a.data.slot < a'.data.slot
    requires inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv)
    requires inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv)
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(dv)
    requires inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_att_duty(dv)
    requires inv_slashing_db_att_in_db_for_low_slot_is_in_db_for_high_slot(dv)
//     ensures && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
//             && !is_slashable_attestation_data_eth_spec(a'.data, a.data)
    {    
        assert  && is_a_valid_decided_value_according_to_set_of_nodes(consa, h_nodes_a)
                && m in h_nodes_a
                ;
        assert  && is_a_valid_decided_value_according_to_set_of_nodes(consa', h_nodes_a')
                && m in h_nodes_a'       
                ;
        
        var m_state := dv.honest_nodes_states[m];
        var slot_a := a.data.slot;
        var slot_a' := a'.data.slot;

        assert consa == dv.consensus_on_attestation_data[slot_a];
        assert consa' == dv.consensus_on_attestation_data[slot_a'];

        var dva := consa.decided_value.safe_get();
        var dva' := consa'.decided_value.safe_get();
        var sdba := construct_SlashingDBAttestation_from_att_data(dva);
        var sdba' := construct_SlashingDBAttestation_from_att_data(dva');
        
        assert consa.honest_nodes_validity_functions[m] != {};
        var vpa: AttestationData -> bool :| && vpa in consa.honest_nodes_validity_functions[m]
                                            && vpa(dva);
        
        assert inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body(dv, m, m_state, slot_a, vpa);
        assert vpa in m_state.attestation_consensus_engine_state.att_slashing_db_hist[slot_a];
        var duty: AttestationDuty, dba :| inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_att_duty_body(dv, m, slot_a, dba, duty, vpa);
        assert sdba in dba;

        assert consa'.honest_nodes_validity_functions[m] != {};
        var vpa': AttestationData -> bool :| && vpa' in consa'.honest_nodes_validity_functions[m]
                                             && vpa'(dva');
        assert inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body(dv, m, m_state, slot_a', vpa');
        assert vpa' in m_state.attestation_consensus_engine_state.att_slashing_db_hist[slot_a'];
        var duty': AttestationDuty, dba' :| inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_att_duty_body(dv, m, slot_a', dba', duty', vpa');
        
        assert inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_att_duty_body(dv, m, slot_a', dba', duty', vpa');
        assert vpa' == (ad': AttestationData) => consensus_is_valid_attestation_data(dba', ad', duty');
        assert !is_slashable_attestation_data(dba', dva');

    
        // Error
        // lem_is_slashable_attestation_data(dba', dva', sdba, sdba');     

        // assert !is_slashable_attestation_data_eth_spec(dva, dva');
        // assert !is_slashable_attestation_data_eth_spec(dva', dva);                 
    }


        // 2nd try in a new version
//     lemma lem_no_slashable_submitted_attestations_with_different_slots_ii(
//                 dv: DVState, 
//                 a: Attestation, 
//                 a': Attestation, 
//                 m: BLSPubkey, 
//                 consa: ConsensusInstance<AttestationData>, consa': ConsensusInstance<AttestationData>,
//                 h_nodes_a: set<BLSPubkey>, h_nodes_a': set<BLSPubkey>)
//     requires |dv.all_nodes| > 0
//     requires inv_quorum_constraints(dv)    
//     requires inv_exists_honest_node_that_contributed_to_decisions_of_consensus_instances(dv, a, a', m, consa, consa', h_nodes_a, h_nodes_a')
//     requires && consa.decided_value.isPresent()
//              && consa'.decided_value.isPresent()
//              && a.data == consa.decided_value.safe_get()
//              && a'.data == consa'.decided_value.safe_get()
//     requires a.data.slot < a'.data.slot
//     requires inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv)
//     requires inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv)
//     requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(dv)
//     requires inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_att_duty(dv)

//     requires inv_attestation_is_created_with_shares_from_quorum(dv)
//     requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(dv)
//     requires inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv)
//     // requires pred_intersection_of_honest_nodes_in_two_quorum_contains_an_honest_node


// //     ensures && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
// //             && !is_slashable_attestation_data_eth_spec(a'.data, a.data)
//     {    
//         assert  && is_a_valid_decided_value_according_to_set_of_nodes(consa, h_nodes_a)
//                 && m in h_nodes_a
//                 ;
//         assert  && is_a_valid_decided_value_according_to_set_of_nodes(consa', h_nodes_a')
//                 && m in h_nodes_a'       
//                 ;
        
//         var m_state := dv.honest_nodes_states[m];
//         var slot_a := a.data.slot;
//         var slot_a' := a'.data.slot;

//         assert consa == dv.consensus_on_attestation_data[slot_a];
//         assert consa' == dv.consensus_on_attestation_data[slot_a'];

//         var dva := consa.decided_value.safe_get();
//         var dva' := consa'.decided_value.safe_get();
//         var sdba := construct_SlashingDBAttestation_from_att_data(dva);
//         var sdba' := construct_SlashingDBAttestation_from_att_data(dva');
        
//         assert consa.honest_nodes_validity_functions[m] != {};
//         var vpa: AttestationData -> bool :| && vpa in consa.honest_nodes_validity_functions[m]
//                                             && vpa(dva);
        
//         assert inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body(dv, m, m_state, slot_a, vpa);
//         assert vpa in m_state.attestation_consensus_engine_state.att_slashing_db_hist[slot_a];
//         var duty: AttestationDuty, dba :| inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_att_duty_body(dv, m, slot_a, dba, duty, vpa);
//         assert sdba in dba;

//         assert consa'.honest_nodes_validity_functions[m] != {};
//         var vpa': AttestationData -> bool :| && vpa' in consa'.honest_nodes_validity_functions[m]
//                                              && vpa'(dva');
//         assert inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body(dv, m, m_state, slot_a', vpa');
//         assert vpa' in m_state.attestation_consensus_engine_state.att_slashing_db_hist[slot_a'];
//         var duty': AttestationDuty, dba' :| inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_att_duty_body(dv, m, slot_a', dba', duty', vpa');
        
//         assert inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_att_duty_body(dv, m, slot_a', dba', duty', vpa');
//         assert vpa' == (ad': AttestationData) => consensus_is_valid_attestation_data(dba', ad', duty');
//         assert !is_slashable_attestation_data(dba', dva');

    
//         // Error
//         // lem_is_slashable_attestation_data(dba', dva', sdba, sdba');     

//         // assert !is_slashable_attestation_data_eth_spec(dva, dva');
//         // assert !is_slashable_attestation_data_eth_spec(dva', dva);                 
//     }

    // lemma lem_no_slashable_submitted_attestations_with_different_slots(dv: DVState, a: Attestation, a': Attestation)
    // requires |dv.all_nodes| > 0
    // requires inv_quorum_constraints(dv)
    // requires inv_unchanged_paras_of_consensus_instances(dv)
    // requires inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv)
    // requires inv_data_of_att_share_is_decided_value(dv)
    // requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(dv)    
    // requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(dv)
    // requires && a in dv.all_attestations_created
    //          && is_valid_attestation(a, dv.dv_pubkey)
    // requires && a' in dv.all_attestations_created
    //          && is_valid_attestation(a', dv.dv_pubkey)
    // requires a.data.slot < a'.data.slot 
    // requires inv_decided_data_has_an_honest_witness(dv)
    // requires inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv)
    // requires inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv)
    // requires inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_att_duty(dv)
    // requires inv_unique_rcvd_att_duty_per_slot(dv)
    // requires inv_active_consensus_instances_implied_the_delivery_of_att_duties(dv)
    // requires inv_data_of_all_created_attestations_is_set_of_decided_values(dv)

    // requires inv_exists_honest_node_that_contributed_to_creation_of_submitted_attestations_body(dv, a, a')
    // requires inv_if_honest_node_sends_att_share_it_receives_att_data_before(dv)
    // ensures && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
    //         && !is_slashable_attestation_data_eth_spec(a'.data, a.data)
    // {
    //     // lem_no_slashable_submitted_attestations_with_different_slots_i(dv, a, a');
        
    //     // var consa := dv.consensus_on_attestation_data[a.data.slot];
    //     // var consa' := dv.consensus_on_attestation_data[a'.data.slot];                      
    //     // var m: BLSPubkey, h_nodes_a: set<BLSPubkey>, h_nodes_a': set<BLSPubkey> :| 
    //     //         inv_exists_honest_node_that_contributed_to_decisions_of_consensus_instances(dv, a, a', m, consa, consa', h_nodes_a, h_nodes_a');

    //     // assert  inv_exists_honest_node_that_contributed_to_decisions_of_consensus_instances(dv, a, a', m, consa, consa', h_nodes_a, h_nodes_a');
    //     // assert  && consa.decided_value.isPresent()
    //     //         && consa'.decided_value.isPresent()
    //     //         ;
    //     // assert  && a.data == consa.decided_value.safe_get()
    //     //         && a'.data == consa'.decided_value.safe_get()
    //     //         ;

    //     // lem_no_slashable_submitted_attestations_with_different_slots_ii(dv, a, a');
    // }    

    lemma lem_no_slashable_submitted_attestations_with_different_slots(dv: DVState, a: Attestation, a': Attestation)
    requires |dv.all_nodes| > 0
    requires inv_quorum_constraints(dv)
    requires inv_unchanged_paras_of_consensus_instances(dv)
    requires inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv)
    requires inv_data_of_att_share_is_decided_value(dv)
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(dv)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(dv)
    requires && a in dv.all_attestations_created
             && is_valid_attestation(a, dv.dv_pubkey)
    requires && a' in dv.all_attestations_created
             && is_valid_attestation(a', dv.dv_pubkey)
    requires a.data.slot < a'.data.slot 
    requires inv_decided_data_has_an_honest_witness(dv)
    requires inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv)
    requires inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv)
    requires inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_att_duty(dv)
    requires inv_unique_rcvd_att_duty_per_slot(dv)
    requires inv_active_consensus_instances_implied_the_delivery_of_att_duties(dv)
    requires inv_data_of_all_created_attestations_is_set_of_decided_values(dv)

    requires inv_attestation_is_created_with_shares_from_quorum(dv)
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(dv)
    requires inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv)
    requires inv_unchanged_paras_of_consensus_instances(dv)
    requires inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate(dv)
    requires inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist(dv)
    // ensures && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
    //         && !is_slashable_attestation_data_eth_spec(a'.data, a.data)
    {
        var data := a.data;
        var data' := a'.data;
        var slot: Slot := data.slot;
        var slot': Slot := data'.slot;
        var consa := dv.consensus_on_attestation_data[slot];
        var consa' := dv.consensus_on_attestation_data[slot'];       
        var dva := consa.decided_value.safe_get();
        var dva' := consa'.decided_value.safe_get();
        var sdba := construct_SlashingDBAttestation_from_att_data(dva);
        var sdba' := construct_SlashingDBAttestation_from_att_data(dva');

        var att_shares: set<AttestationShare>, signers: set<BLSPubkey> :| inv_attestation_is_created_with_shares_from_quorum_body(dv, a, att_shares, signers);            
        assert  && signers <= dv.all_nodes
                && inv_attestation_is_created_with_shares_from_quorum_body_signers(dv, att_shares, signers)
                && |signers| >= quorum(|dv.all_nodes|)           
            ;

        var h_nodes': set<BLSPubkey> :| is_a_valid_decided_value_according_to_set_of_nodes(consa', h_nodes');
        assert dv.adversary.nodes == consa'.all_nodes - consa'.honest_nodes_status.Keys;
        assert h_nodes' * dv.adversary.nodes == {};
        calc {
            |h_nodes' + dv.adversary.nodes|;
            ==
            |h_nodes'| + |dv.adversary.nodes|;
            >=
            quorum(|dv.all_nodes|);
        }

        var voters' := h_nodes' + dv.adversary.nodes;
        var hnodes := dv.all_nodes - dv.adversary.nodes; 
        assert hnodes == dv.honest_nodes_states.Keys;
    
        lemmaQuorumIntersection(
            dv.all_nodes,
            dv.adversary.nodes,
            signers,
            voters'
        );
        assert signers * voters' * hnodes != {};

        lemmDoubleIntersections(signers, voters', hnodes);
        assert exists hn: BLSPubkey :: 
                && hn in signers
                && hn in voters'
                && hn in hnodes
                ; 

        var m: BLSPubkey :| 
                && m in signers
                && m in voters'
                && m in hnodes
                ;
        assert  is_honest_node(dv, m);
        assert  inv_attestation_is_created_with_shares_from_quorum_body_signers_helper(
                    dv, 
                    att_shares,
                    m
                );
        assert  exists att_share: AttestationShare ::
                    && att_share in att_shares
                    && pred_verify_owner_of_attestation_share_with_bls_signature(m, att_share)
                    ;
        
        var att_share: AttestationShare :| 
            && att_share in att_shares
            && pred_verify_owner_of_attestation_share_with_bls_signature(m, att_share)
            ;
        assert att_share.data == dva;

        var dvc := dv.honest_nodes_states[m];
        assert inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate_body(dvc);

        var vp': AttestationData -> bool :|
                && vp' in consa'.honest_nodes_validity_functions[m] 
                && vp'(consa'.decided_value.safe_get())  
                ;
        assert inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body(
                        dv,
                        m,
                        dvc,
                        slot',
                        vp'
                    );
        assert  vp' in dvc.attestation_consensus_engine_state.att_slashing_db_hist[slot'];
        assert  slot' in dvc.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
        
        var db': set<SlashingDBAttestation>, duty': AttestationDuty :| 
                && duty'.slot == slot'
                && db' in dvc.attestation_consensus_engine_state.att_slashing_db_hist[slot'][vp']
                && vp' == (ad: AttestationData) => consensus_is_valid_attestation_data(db', ad, duty')
                ;
        assert consensus_is_valid_attestation_data(db', data', duty');
        assert !is_slashable_attestation_data(db', data');
        assert inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots_body(
                        dv,
                        m, 
                        slot', 
                        vp', 
                        db'
                    );
        assert sdba in db';

        lem_is_slashable_attestation_data(db', dva', sdba, sdba');   

        assert  && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
                && !is_slashable_attestation_data_eth_spec(a'.data, a.data)
                ;


        // var m: BLSPubkey, h_nodes_a: set<BLSPubkey>, h_nodes_a': set<BLSPubkey> :| 
        //         inv_exists_honest_node_that_contributed_to_decisions_of_consensus_instances(dv, a, a', m, consa, consa', h_nodes_a, h_nodes_a');

        // assert  inv_exists_honest_node_that_contributed_to_decisions_of_consensus_instances(dv, a, a', m, consa, consa', h_nodes_a, h_nodes_a');
        // assert  && consa.decided_value.isPresent()
        //         && consa'.decided_value.isPresent()
        //         ;
        // assert  && a.data == consa.decided_value.safe_get()
        //         && a'.data == consa'.decided_value.safe_get()
        //         ;

    } 

    lemma lem_no_slashable_submitted_attestations_with_same_slots(dv: DVState, a: Attestation, a': Attestation)
    requires |dv.all_nodes| > 0
    requires inv_quorum_constraints(dv)
    requires inv_unchanged_paras_of_consensus_instances(dv)
    requires inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv)
    requires inv_data_of_att_share_is_decided_value(dv)
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(dv)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(dv)
    requires && a in dv.all_attestations_created
             && is_valid_attestation(a, dv.dv_pubkey)
    requires && a' in dv.all_attestations_created
             && is_valid_attestation(a', dv.dv_pubkey)
    requires a.data.slot == a'.data.slot 
    ensures && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
            && !is_slashable_attestation_data_eth_spec(a'.data, a.data)
    {
        var hna, att_share, fv :|
                && hna in dv.honest_nodes_states.Keys 
                && att_share in dv.att_network.allMessagesSent
                && att_share.data == a.data
                && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fv);
                && verify_bls_siganture(attestation_signing_root, att_share.signature, hna);     

        var hna', att_share', fv' :|
                && hna' in dv.honest_nodes_states.Keys 
                && att_share' in dv.att_network.allMessagesSent
                && att_share'.data == a'.data
                && var attestation_signing_root := compute_attestation_signing_root(att_share'.data, fv');
                && verify_bls_siganture(attestation_signing_root, att_share'.signature, hna');   

        var cons := dv.consensus_on_attestation_data[a.data.slot];                 

        assert  && cons.decided_value.isPresent()
                && cons.decided_value.safe_get() == att_share.data
                && cons.decided_value.safe_get() == att_share'.data;     

        assert a.data == a'.data;  

        assert !is_slashable_attestation_data_eth_spec(a.data, a'.data);
        assert !is_slashable_attestation_data_eth_spec(a'.data, a.data);        
    }      

    lemma lem_no_slashable_submitted_attestations(dv: DVState, a: Attestation, a': Attestation)    
    requires |dv.all_nodes| > 0
    requires inv_quorum_constraints(dv)
    requires inv_unchanged_paras_of_consensus_instances(dv)
    requires inv_exists_honest_dvc_that_sent_att_share_for_submitted_att(dv)
    requires inv_data_of_att_share_is_decided_value(dv)
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(dv)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_att_duty_and_slashing_db(dv)
    requires && a in dv.all_attestations_created
             && is_valid_attestation(a, dv.dv_pubkey)
    requires && a' in dv.all_attestations_created
             && is_valid_attestation(a', dv.dv_pubkey)
    requires inv_decided_data_has_an_honest_witness(dv)
    requires inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv)
    requires inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv)
    requires inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_att_duty(dv)
    requires inv_unique_rcvd_att_duty_per_slot(dv)
    requires inv_active_consensus_instances_implied_the_delivery_of_att_duties(dv)
    requires inv_data_of_all_created_attestations_is_set_of_decided_values(dv)
    
    requires inv_exists_honest_node_that_contributed_to_creation_of_submitted_attestations_body(dv, a, a')
    requires inv_if_honest_node_sends_att_share_it_receives_att_data_before(dv)        
    ensures && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
            && !is_slashable_attestation_data_eth_spec(a'.data, a.data)   
    {
        if a.data.slot == a'.data.slot 
        {
            lem_no_slashable_submitted_attestations_with_same_slots(dv, a, a');
        }
        else if a.data.slot < a'.data.slot 
        {
            lem_no_slashable_submitted_attestations_with_different_slots(dv, a, a');
        }
        else {
            lem_no_slashable_submitted_attestations_with_different_slots(dv, a', a);
        }
    } 

}