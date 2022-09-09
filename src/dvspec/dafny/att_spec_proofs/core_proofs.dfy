include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/ind_inv.dfy"
include "../att_spec_proofs/helper_sets_lemmas.dfy"

module Core_Proofs
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Att_Ind_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Helper_Sets_Lemmas


    predicate is_slashable_attestation_data_eth_spec(data_1: AttestationData, data_2: AttestationData)
    {
        || (data_1 != data_2 && data_1.target.epoch == data_2.target.epoch)
        || (data_1.source.epoch < data_2.source.epoch && data_2.target.epoch < data_1.target.epoch)
    }


    lemma lemma_4_1_a_ii(dvn: DVState, a: Attestation, a': Attestation, m: BLSPubkey, 
                        consa: ConsensusInstance<AttestationData>, consa': ConsensusInstance<AttestationData>,
                        h_nodes_a: set<BLSPubkey>, h_nodes_a': set<BLSPubkey>)
    requires |dvn.all_nodes| > 0
    requires inv52(dvn)    
    requires pred_4_1_witness(dvn, a, a', m, consa, consa', h_nodes_a, h_nodes_a')
    requires && consa.decided_value.isPresent()
             && consa'.decided_value.isPresent()
             && a.data == consa.decided_value.safe_get()
             && a'.data == consa'.decided_value.safe_get()
    requires && is_a_valid_decided_value_according_to_set_of_nodes(consa', h_nodes_a')
             && m in h_nodes_a'             
    requires a.data.slot < a'.data.slot
    requires inv48(dvn)
    requires inv47(dvn)
    requires inv46_a(dvn)
    requires inv46_b(dvn)
    requires pred_4_1_g_i(dvn)
    requires pred_4_1_g_ii(dvn)
    requires inv50(dvn)
    requires inv49(dvn)
    requires inv51(dvn)
    ensures && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
            && !is_slashable_attestation_data_eth_spec(a'.data, a.data)
    {        
        var m_state := dvn.honest_nodes_states[m];
        var sa := a.data.slot;
        var sa' := a'.data.slot;
        var consa := dvn.consensus_on_attestation_data[sa];
        var consa' := dvn.consensus_on_attestation_data[sa'];  
        var dva := consa.decided_value.safe_get();
        var dva' := consa'.decided_value.safe_get();
        var sdba := construct_SlashingDBAttestation_from_att_data(dva);
        var sdba' := construct_SlashingDBAttestation_from_att_data(dva');
        
        assert consa'.honest_nodes_validity_functions[m] != {};
        var vpa': AttestationData -> bool :| && vpa' in consa'.honest_nodes_validity_functions[m]
                                             && vpa'(consa'.decided_value.safe_get());

        assert inv46_b_body(dvn, m, sa', vpa');
        assert vpa' in m_state.att_slashing_db_hist[sa'];
        
        var dba': set<SlashingDBAttestation> := m_state.att_slashing_db_hist[sa'][vpa'];  

        assert inv51_body(m_state, sa');
        var duty: AttestationDuty :| duty in m_state.all_rcvd_duties && duty.slot == sa';
        
        assert inv50_body(dvn, m, sa', dba', duty, vpa');
        assert vpa' == (ad: AttestationData) => consensus_is_valid_attestation_data(dba', ad, duty);
        assert !is_slashable_attestation_data(dba', dva');

        lemma_is_slashable_attestation_data(dba', dva', sdba', sdba);        
        assert !is_slashable_attestation_data_eth_spec(dva, dva');
        assert !is_slashable_attestation_data_eth_spec(dva', dva);                 
    }


    lemma lemma_4_1_a_i(dvn: DVState, a: Attestation, a': Attestation, hn: BLSPubkey, hn': BLSPubkey)
    requires |dvn.all_nodes| > 0
    requires inv52(dvn)
    requires pred_4_1_b(dvn)
    requires pred_4_1_c(dvn)
    requires pred_4_1_f_a(dvn)
    requires inv42(dvn)   
    requires hn in dvn.honest_nodes_states.Keys 
    requires hn' in dvn.honest_nodes_states.Keys
    requires a in dvn.honest_nodes_states[hn].bn.attestations_submitted
    requires a' in dvn.honest_nodes_states[hn'].bn.attestations_submitted
    requires a.data.slot < a'.data.slot 
    ensures && var consa := dvn.consensus_on_attestation_data[a.data.slot];
            && var consa' := dvn.consensus_on_attestation_data[a'.data.slot];   
            && exists m: BLSPubkey, h_nodes_a: set<BLSPubkey>, h_nodes_a': set<BLSPubkey> :: 
                        pred_4_1_witness(dvn, a, a', m, consa, consa', h_nodes_a, h_nodes_a')    
    {
        var hna, att_share :|
                && is_honest_node(dvn, hna)
                && att_share in dvn.att_network.allMessagesSent
                && att_share.data == a.data
                && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));
                && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
                && verify_bls_siganture(attestation_signing_root, att_share.signature, hna);     

        var hna', att_share' :|
                && is_honest_node(dvn, hna)
                && att_share' in dvn.att_network.allMessagesSent
                && att_share'.data == a'.data
                && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share'.data.target.epoch));
                && var attestation_signing_root := compute_attestation_signing_root(att_share'.data, fork_version);
                && verify_bls_siganture(attestation_signing_root, att_share'.signature, hna');  

        assert
                && dvn.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent()
                && dvn.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;       

        assert
                && dvn.consensus_on_attestation_data[att_share'.data.slot].decided_value.isPresent()
                && dvn.consensus_on_attestation_data[att_share'.data.slot].decided_value.safe_get() == att_share'.data;   

        var consa := dvn.consensus_on_attestation_data[a.data.slot];
        var consa' := dvn.consensus_on_attestation_data[a'.data.slot];                    

        assert is_a_valid_decided_value(consa); 
        assert is_a_valid_decided_value(consa');  

        assert consa.decided_value.isPresent();

        var h_nodes_a :| is_a_valid_decided_value_according_to_set_of_nodes(consa, h_nodes_a);
        var h_nodes_a' :| is_a_valid_decided_value_according_to_set_of_nodes(consa', h_nodes_a');

        assert consa.all_nodes == consa'.all_nodes == dvn.all_nodes;

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

        assert pred_4_1_witness(dvn, a, a', m, consa, consa', h_nodes_a, h_nodes_a');
        assert ( exists m: BLSPubkey, h_nodes_a: set<BLSPubkey>, h_nodes_a': set<BLSPubkey> :: 
                                pred_4_1_witness(dvn, a, a', m, consa, consa', h_nodes_a, h_nodes_a') ); 
    }



    lemma lemma_4_1_a(dvn: DVState, a: Attestation, a': Attestation, hn: BLSPubkey, hn': BLSPubkey)
    requires |dvn.all_nodes| > 0
    requires inv52(dvn)
    requires pred_4_1_b(dvn)
    requires pred_4_1_c(dvn)
    requires pred_4_1_f_a(dvn)
    requires inv42(dvn)
    requires pred_4_1_g_i(dvn)
    requires pred_4_1_g_ii(dvn)
    requires hn in dvn.honest_nodes_states.Keys 
    requires hn' in dvn.honest_nodes_states.Keys
    requires a in dvn.honest_nodes_states[hn].bn.attestations_submitted
    requires a' in dvn.honest_nodes_states[hn'].bn.attestations_submitted
    requires a.data.slot < a'.data.slot 
    requires inv48(dvn)
    requires inv47(dvn)
    requires inv46_a(dvn)
    requires inv46_b(dvn)
    requires inv50(dvn)
    requires inv49(dvn)
    requires inv51(dvn)
    ensures && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
            && !is_slashable_attestation_data_eth_spec(a'.data, a.data)
    {
        lemma_4_1_a_i(dvn, a, a', hn, hn');

        
        var consa := dvn.consensus_on_attestation_data[a.data.slot];
        var consa' := dvn.consensus_on_attestation_data[a'.data.slot];                      
        var m: BLSPubkey, h_nodes_a: set<BLSPubkey>, h_nodes_a': set<BLSPubkey> :| 
                pred_4_1_witness(dvn, a, a', m, consa, consa', h_nodes_a, h_nodes_a');

        
        assert pred_4_1_witness(dvn, a, a', m, consa, consa', h_nodes_a, h_nodes_a');
        lemma_4_1_a_ii(dvn, a, a', m, consa, consa', h_nodes_a, h_nodes_a');
        
    }    

    lemma lemma_4_1_b(dvn: DVState, a: Attestation, a': Attestation, hn: BLSPubkey, hn': BLSPubkey)
    requires |dvn.all_nodes| > 0
    requires inv52(dvn)
    requires pred_4_1_b(dvn)
    requires pred_4_1_c(dvn)
    requires pred_4_1_f_a(dvn)
    requires inv42(dvn)
    requires pred_4_1_g_i(dvn)
    requires pred_4_1_g_ii(dvn)
    requires hn in dvn.honest_nodes_states.Keys 
    requires hn' in dvn.honest_nodes_states.Keys
    requires a in dvn.honest_nodes_states[hn].bn.attestations_submitted
    requires a' in dvn.honest_nodes_states[hn'].bn.attestations_submitted
    requires a.data.slot == a'.data.slot 
    ensures && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
            && !is_slashable_attestation_data_eth_spec(a'.data, a.data)
    {
        var hna, att_share :|
                && hna in dvn.honest_nodes_states.Keys 
                && att_share in dvn.att_network.allMessagesSent
                && att_share.data == a.data
                && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));
                && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
                && verify_bls_siganture(attestation_signing_root, att_share.signature, hna);     

        var hna', att_share' :|
                && hna' in dvn.honest_nodes_states.Keys 
                && att_share' in dvn.att_network.allMessagesSent
                && att_share'.data == a'.data
                && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share'.data.target.epoch));
                && var attestation_signing_root := compute_attestation_signing_root(att_share'.data, fork_version);
                && verify_bls_siganture(attestation_signing_root, att_share'.signature, hna');  

        var cons := dvn.consensus_on_attestation_data[a.data.slot];                 

        assert
                && cons.decided_value.isPresent()
                && cons.decided_value.safe_get() == att_share.data
                && cons.decided_value.safe_get() == att_share'.data;     

        assert a.data == a'.data;  

        assert !is_slashable_attestation_data_eth_spec(a.data, a'.data);
        assert !is_slashable_attestation_data_eth_spec(a'.data, a.data);        
    }      


    lemma lemma_4_1_general(dvn: DVState, a: Attestation, a': Attestation, hn: BLSPubkey, hn': BLSPubkey)
    requires |dvn.all_nodes| > 0
    requires inv52(dvn)
    requires pred_4_1_b(dvn)
    requires pred_4_1_c(dvn)
    requires pred_4_1_f_a(dvn)
    requires inv42(dvn)
    requires pred_4_1_g_i(dvn)
    requires pred_4_1_g_ii(dvn)
    requires hn in dvn.honest_nodes_states.Keys 
    requires hn' in dvn.honest_nodes_states.Keys
    requires a in dvn.honest_nodes_states[hn].bn.attestations_submitted
    requires a' in dvn.honest_nodes_states[hn'].bn.attestations_submitted
    requires inv48(dvn)
    requires inv47(dvn)
    requires inv46_a(dvn)
    requires inv46_b(dvn)
    requires inv50(dvn)
    requires inv49(dvn)
    requires inv51(dvn)
    ensures && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
            && !is_slashable_attestation_data_eth_spec(a'.data, a.data)   
    {
        if a.data.slot == a'.data.slot 
        {
            lemma_4_1_b(dvn, a, a', hn, hn');
        }
        else if a.data.slot < a'.data.slot 
        {
            lemma_4_1_a(dvn, a, a', hn, hn');
        }
        else {
            lemma_4_1_a(dvn, a', a, hn', hn);
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