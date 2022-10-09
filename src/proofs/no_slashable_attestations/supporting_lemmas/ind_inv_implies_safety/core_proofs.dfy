include "../../../../common/commons.dfy"
include "../../common/attestation_creation_instrumented.dfy"
include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_attestation_creation.dfy"

include "../../../common/helper_sets_lemmas.dfy"

include "../dv_next_preserves_ind_inv/invs_dv_next_1.dfy"
include "../dv_next_preserves_ind_inv/invs_dv_next_2.dfy"
include "../dv_next_preserves_ind_inv/invs_fnc_1.dfy"
include "../dv_next_preserves_ind_inv/invs_fnc_2.dfy"
include "../dv_next_preserves_ind_inv/invs_dv_next_3.dfy"
include "../dv_next_preserves_ind_inv/invs_dv_next_4.dfy"
include "../dv_next_preserves_ind_inv/invs_dv_next_5.dfy"
include "../dv_next_preserves_ind_inv/invs_dv_next_6.dfy"

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


    lemma lemma_4_1_a_ii(dv: DVState, a: Attestation, a': Attestation, m: BLSPubkey, 
                        consa: ConsensusInstance<AttestationData>, consa': ConsensusInstance<AttestationData>,
                        h_nodes_a: set<BLSPubkey>, h_nodes_a': set<BLSPubkey>)
    requires |dv.all_nodes| > 0
    requires inv_quorum_constraints(dv)    
    requires pred_4_1_witness(dv, a, a', m, consa, consa', h_nodes_a, h_nodes_a')
    requires && consa.decided_value.isPresent()
             && consa'.decided_value.isPresent()
             && a.data == consa.decided_value.safe_get()
             && a'.data == consa'.decided_value.safe_get()
    requires && is_a_valid_decided_value_according_to_set_of_nodes(consa', h_nodes_a')
             && m in h_nodes_a'             
    requires a.data.slot < a'.data.slot
    requires inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv)
    requires inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv)
    requires pred_4_1_g_i(dv)
    requires pred_4_1_g_iii(dv)
    requires inv_queued_att_duty_is_rcvd_duty0(dv)
    // requires inv_queued_att_duty_is_rcvd_duty1(dv)
    ensures && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
            && !is_slashable_attestation_data_eth_spec(a'.data, a.data)
    {        
        var m_state := dv.honest_nodes_states[m];
        var sa := a.data.slot;
        var sa' := a'.data.slot;
        var consa := dv.consensus_on_attestation_data[sa];
        var consa' := dv.consensus_on_attestation_data[sa'];  
        var dva := consa.decided_value.safe_get();
        var dva' := consa'.decided_value.safe_get();
        var sdba := construct_SlashingDBAttestation_from_att_data(dva);
        var sdba' := construct_SlashingDBAttestation_from_att_data(dva');
        
        assert consa'.honest_nodes_validity_functions[m] != {};
        var vpa': AttestationData -> bool :| && vpa' in consa'.honest_nodes_validity_functions[m]
                                             && vpa'(consa'.decided_value.safe_get());

        // assert inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body(dv, m, sa', vpa');
        assert inv_all_validity_predicates_are_stored_in_att_slashing_db_hist_body(dv, m, m_state, sa', vpa');
        assert vpa' in m_state.attestation_consensus_engine_state.att_slashing_db_hist[sa'];
        
        // var dba': set<SlashingDBAttestation> := m_state.attestation_consensus_engine_state.att_slashing_db_hist[sa'][vpa'];  

        // assert inv_queued_att_duty_is_rcvd_duty1_body(m_state, sa');
        var duty: AttestationDuty, dba' :| inv_queued_att_duty_is_rcvd_duty0_body(dv, m, sa', dba', duty, vpa');
        
        assert inv_queued_att_duty_is_rcvd_duty0_body(dv, m, sa', dba', duty, vpa');
        assert vpa' == (ad: AttestationData) => consensus_is_valid_attestation_data(dba', ad, duty);
        assert !is_slashable_attestation_data(dba', dva');

        lemma_is_slashable_attestation_data(dba', dva', sdba', sdba);        
        assert !is_slashable_attestation_data_eth_spec(dva, dva');
        assert !is_slashable_attestation_data_eth_spec(dva', dva);                 
    }


    lemma lemma_4_1_a_i(dv: DVState, a: Attestation, a': Attestation)
    requires |dv.all_nodes| > 0
    requires inv_quorum_constraints(dv)   
    requires inv_unchanged_honesty(dv)
    requires pred_4_1_b(dv)
    requires pred_4_1_c(dv)
    requires pred_4_1_f_a(dv)    
    requires && a in dv.all_attestations_created
             && is_valid_attestation(a, dv.dv_pubkey)
    requires && a' in dv.all_attestations_created
             && is_valid_attestation(a', dv.dv_pubkey)
    requires a.data.slot < a'.data.slot 
    ensures && var consa := dv.consensus_on_attestation_data[a.data.slot];
            && var consa' := dv.consensus_on_attestation_data[a'.data.slot];   
            && exists m: BLSPubkey, h_nodes_a: set<BLSPubkey>, h_nodes_a': set<BLSPubkey> :: 
                        pred_4_1_witness(dv, a, a', m, consa, consa', h_nodes_a, h_nodes_a')    
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

        assert pred_4_1_witness(dv, a, a', m, consa, consa', h_nodes_a, h_nodes_a');
        assert ( exists m: BLSPubkey, h_nodes_a: set<BLSPubkey>, h_nodes_a': set<BLSPubkey> :: 
                                pred_4_1_witness(dv, a, a', m, consa, consa', h_nodes_a, h_nodes_a') ); 
    }

    lemma lemma_4_1_a(dv: DVState, a: Attestation, a': Attestation)
    requires |dv.all_nodes| > 0
    requires inv_quorum_constraints(dv)
    requires inv_unchanged_honesty(dv)
    requires pred_4_1_b(dv)
    requires pred_4_1_c(dv)
    requires pred_4_1_f_a(dv)    
    requires pred_4_1_g_i(dv)
    requires pred_4_1_g_iii(dv)
    requires && a in dv.all_attestations_created
             && is_valid_attestation(a, dv.dv_pubkey)
    requires && a' in dv.all_attestations_created
             && is_valid_attestation(a', dv.dv_pubkey)
    requires a.data.slot < a'.data.slot 
//     requires inv_queued_att_duty_is_dvn_seq_of_att_duty8(dv)
//     requires inv_queued_att_duty_is_dvn_seq_of_att_duty7(dv)
    requires inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv)
    requires inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv)
    requires inv_queued_att_duty_is_rcvd_duty0(dv)
//     requires inv_queued_att_duty_is_dvn_seq_of_att_duty9(dv)
    requires inv_queued_att_duty_is_rcvd_duty1(dv)
    ensures && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
            && !is_slashable_attestation_data_eth_spec(a'.data, a.data)
    {
        lemma_4_1_a_i(dv, a, a');

        
        var consa := dv.consensus_on_attestation_data[a.data.slot];
        var consa' := dv.consensus_on_attestation_data[a'.data.slot];                      
        var m: BLSPubkey, h_nodes_a: set<BLSPubkey>, h_nodes_a': set<BLSPubkey> :| 
                pred_4_1_witness(dv, a, a', m, consa, consa', h_nodes_a, h_nodes_a');

        
        assert pred_4_1_witness(dv, a, a', m, consa, consa', h_nodes_a, h_nodes_a');
        lemma_4_1_a_ii(dv, a, a', m, consa, consa', h_nodes_a, h_nodes_a');
        
    }    

    lemma lemma_4_1_b(dv: DVState, a: Attestation, a': Attestation)
    requires |dv.all_nodes| > 0
    requires inv_quorum_constraints(dv)
    requires inv_unchanged_honesty(dv)
    requires pred_4_1_b(dv)
    requires pred_4_1_c(dv)
    requires pred_4_1_f_a(dv)    
    requires pred_4_1_g_i(dv)
    requires pred_4_1_g_iii(dv)
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

        assert
                && cons.decided_value.isPresent()
                && cons.decided_value.safe_get() == att_share.data
                && cons.decided_value.safe_get() == att_share'.data;     

        assert a.data == a'.data;  

        assert !is_slashable_attestation_data_eth_spec(a.data, a'.data);
        assert !is_slashable_attestation_data_eth_spec(a'.data, a.data);        
    }      


    lemma lemma_4_1_general(dv: DVState, a: Attestation, a': Attestation)    
    requires inv_quorum_constraints(dv)
    requires inv_unchanged_honesty(dv)
    requires pred_4_1_b(dv)
    requires pred_4_1_c(dv)
    requires pred_4_1_f_a(dv)    
    requires pred_4_1_g_i(dv)
    requires pred_4_1_g_iii(dv)
    requires && a in dv.all_attestations_created
             && is_valid_attestation(a, dv.dv_pubkey)
    requires && a' in dv.all_attestations_created
             && is_valid_attestation(a', dv.dv_pubkey)
    requires inv_sent_validity_predicate_only_for_slots_stored_in_att_slashing_db_hist(dv)
    requires inv_all_validity_predicates_are_stored_in_att_slashing_db_hist(dv)
    requires inv_queued_att_duty_is_rcvd_duty0(dv)
    requires inv_queued_att_duty_is_rcvd_duty1(dv)
    ensures && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
            && !is_slashable_attestation_data_eth_spec(a'.data, a.data)   
    {
        if a.data.slot == a'.data.slot 
        {
            lemma_4_1_b(dv, a, a');
        }
        else if a.data.slot < a'.data.slot 
        {
            lemma_4_1_a(dv, a, a');
        }
        else {
            lemma_4_1_a(dv, a', a);
        }
    } 


    lemma lemma_is_slashable_attestation_data(
        att_slashing_db: set<SlashingDBAttestation>, 
        ad: AttestationData,
        sdba: SlashingDBAttestation,
        sdba': SlashingDBAttestation

    )
    requires !is_slashable_attestation_data(att_slashing_db, ad)
    requires sdba' in att_slashing_db
    requires sdba.source_epoch == ad.source.epoch 
    requires sdba.target_epoch == ad.target.epoch 
    ensures !is_slashable_attestation_pair(sdba, sdba')
    ensures !is_slashable_attestation_pair(sdba', sdba)
    {

    }
        
}