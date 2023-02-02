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
    import opened Invs_DV_Next_5
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

    lemma lem_no_slashable_submitted_attestations_with_different_slots(dv: DVState, a: Attestation, a': Attestation)
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
    requires inv_data_of_all_created_attestations_is_set_of_decided_values(dv)
    requires inv_unique_rcvd_att_duty_per_slot(dv)
    requires inv_active_consensus_instances_implied_the_delivery_of_att_duties(dv)
    requires inv_attestation_is_created_with_shares_from_quorum(dv)
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(dv)
    requires inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv)
    requires inv_unchanged_paras_of_consensus_instances(dv)
    requires inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate(dv)
    requires inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist(dv)
    requires inv_unchanged_dvc_rs_pubkey(dv)
    ensures && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
            && !is_slashable_attestation_data_eth_spec(a'.data, a.data)
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

        var att_shares: set<AttestationShare>, signers: set<BLSPubkey> :| 
                && att_shares <= dv.att_network.allMessagesSent
                && var constructed_sig := dv.construct_signed_attestation_signature(att_shares);
                && constructed_sig.isPresent()
                && constructed_sig.safe_get() == a.signature
                && do_all_att_shares_have_the_same_data(att_shares, a.data)
                && signers <= dv.all_nodes
                && inv_attestation_is_created_with_shares_from_quorum_body_signers(dv, att_shares, signers)
                && |signers| >= quorum(|dv.all_nodes|)
                && signers <= dv.all_nodes
                ;
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
                    att_shares,
                    dv.honest_nodes_states[m]
                );
        assert dv.honest_nodes_states[m].rs.pubkey == m;
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
    } 

    lemma lem_no_slashable_submitted_attestations_with_same_slots(dv: DVState, a: Attestation, a': Attestation)
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
                && verify_bls_signature(attestation_signing_root, att_share.signature, hna);     

        var hna', att_share', fv' :|
                && hna' in dv.honest_nodes_states.Keys 
                && att_share' in dv.att_network.allMessagesSent
                && att_share'.data == a'.data
                && var attestation_signing_root := compute_attestation_signing_root(att_share'.data, fv');
                && verify_bls_signature(attestation_signing_root, att_share'.signature, hna');   

        var cons := dv.consensus_on_attestation_data[a.data.slot];                 

        assert  && cons.decided_value.isPresent()
                && cons.decided_value.safe_get() == att_share.data
                && cons.decided_value.safe_get() == att_share'.data;     

        assert a.data == a'.data;  

        assert !is_slashable_attestation_data_eth_spec(a.data, a'.data);
        assert !is_slashable_attestation_data_eth_spec(a'.data, a.data);        
    }      

    lemma lem_no_slashable_submitted_attestations(dv: DVState, a: Attestation, a': Attestation)    
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
    requires inv_decided_value_of_consensus_instance_is_decided_by_quorum(dv)
    requires inv_unchanged_paras_of_consensus_instances(dv)
    requires inv_exists_db_in_att_slashing_db_hist_and_duty_for_every_validity_predicate(dv)
    requires inv_slots_for_sent_validity_predicate_are_stored_in_att_slashing_db_hist(dv)
    requires inv_attestation_is_created_with_shares_from_quorum(dv)
    requires inv_db_of_vp_contains_all_att_data_of_sent_att_shares_for_lower_slots(dv)
    requires inv_unchanged_dvc_rs_pubkey(dv)
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