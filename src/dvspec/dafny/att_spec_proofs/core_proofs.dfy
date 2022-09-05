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

/*
    lemma core_invariants_imply_safety(dvn: DVState)
    requires pred37c_in_sec_3_8(dvn)    
    requires pred40(dvn)
    // ensures safety(dvn)
    {
        var pubkey: BLSPubkey :| 
                && is_honest_node(dvn, pubkey)
                && dvn.globally_signed_attestations <= seqToSet(dvn.honest_nodes_states[pubkey].bn.attestations_submitted);
        var s := dvn.honest_nodes_states[pubkey];                
        var attestations := seqToSet(s.bn.attestations_submitted);
        var unchecked_attestations := dvn.globally_signed_attestations;
        var checked_attestations: set<Attestation> := {};
        
        while unchecked_attestations != {}
            invariant unchecked_attestations <= dvn.globally_signed_attestations
            invariant unchecked_attestations + checked_attestations == dvn.globally_signed_attestations
            invariant dvn.globally_signed_attestations <= attestations 
            decreases |unchecked_attestations|
        {
            var a: Attestation :| a in unchecked_attestations;
            assert a in dvn.globally_signed_attestations;
            assert a in attestations;

            var tempSet := dvn.globally_signed_attestations - { a };
            assert tempSet <= attestations;

            unchecked_attestations := unchecked_attestations - { a };   
            checked_attestations := checked_attestations + { a };
        }
    }
    */
    

    lemma core_invariants_imply_safety(dvn: DVState)
    requires pred37c_in_sec_3_8(dvn)    
    requires pred40(dvn)
    ensures safety(dvn)
    {
        var pubkey: BLSPubkey :| 
                && is_honest_node(dvn, pubkey)
                && dvn.globally_signed_attestations <= seqToSet(dvn.honest_nodes_states[pubkey].bn.attestations_submitted);
        var s := dvn.honest_nodes_states[pubkey];                
        var attestations := seqToSet(s.bn.attestations_submitted);
        assert dvn.globally_signed_attestations <= attestations;

        var unchecked_attestations := dvn.globally_signed_attestations;
        var checked_attestations: set<Attestation> := {};

        while unchecked_attestations != {}
            invariant unchecked_attestations <= dvn.globally_signed_attestations
            invariant unchecked_attestations + checked_attestations == dvn.globally_signed_attestations
            invariant dvn.globally_signed_attestations <= attestations 
            invariant is_honest_node(dvn, pubkey)
            invariant forall a: Attestation :: 
                            a in checked_attestations 
                                ==> && var tempSet := dvn.globally_signed_attestations - { a };
                                    && !is_slashable_attestation_data_in_set_of_attestations(tempSet, a.data);
            decreases |unchecked_attestations|
        {
            var a: Attestation :| a in unchecked_attestations;
            assert a in dvn.globally_signed_attestations;
            assert a in attestations;

            var tempSet := dvn.globally_signed_attestations - { a };
            assert tempSet <= attestations;

            assert !is_slashable_attestation_data_in_set_of_attestations(tempSet, a.data);

            unchecked_attestations := unchecked_attestations - { a };   
            checked_attestations := checked_attestations + { a };
        }
        

        assert checked_attestations == dvn.globally_signed_attestations;
        assert forall a: Attestation :: 
                    a in dvn.globally_signed_attestations
                        ==> && var tempSet := dvn.globally_signed_attestations - { a };
                            && !is_slashable_attestation_data_in_set_of_attestations(tempSet, a.data);
    }
    predicate is_slashable_attestation_data_eth_spec(data_1: AttestationData, data_2: AttestationData)
    {
        || (data_1 != data_2 && data_1.target.epoch == data_2.target.epoch)
        || (data_1.source.epoch < data_2.source.epoch && data_2.target.epoch < data_1.target.epoch)
    }


    lemma lemma_4_1_a(dvn: DVState, a: Attestation, a': Attestation, hn: BLSPubkey, hn': BLSPubkey)
    requires |dvn.all_nodes| > 0
    requires pred_4_1_b(dvn)
    requires pred_4_1_c(dvn)
    requires pred_4_1_f_a(dvn)
    requires inv42(dvn)
    requires pred_4_1_g_a(dvn)
    requires pred_4_1_g_b(dvn)
    requires hn in dvn.honest_nodes_states.Keys 
    requires hn' in dvn.honest_nodes_states.Keys
    requires a in dvn.honest_nodes_states[hn].bn.attestations_submitted
    requires a' in dvn.honest_nodes_states[hn'].bn.attestations_submitted
    requires a.data.slot < a'.data.slot 
    requires isConditionForSafetyTrue(dvn.consensus_on_attestation_data[a.data.slot])
    requires isConditionForSafetyTrue(dvn.consensus_on_attestation_data[a'.data.slot])
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

        assert m in  consa.honest_nodes_validity_functions.Keys; 
        assert m in  consa'.honest_nodes_validity_functions.Keys; 

        var vpa: AttestationData -> bool :| 
            vpa in consa.honest_nodes_validity_functions[m] && vpa(consa.decided_value.safe_get()); 

        var vpa': AttestationData -> bool :| 
            vpa' in consa'.honest_nodes_validity_functions[m] && vpa'(consa'.decided_value.safe_get()); 

        var attestation_duty', attestation_slashing_db' :|
                vpa' == (ad: AttestationData) => consensus_is_valid_attestation_data(attestation_slashing_db', ad, attestation_duty');   

        assert consa.decided_value.isPresent();  

        var decided_a_data := consa.decided_value.safe_get();
        var sdba := SlashingDBAttestation(
                                        source_epoch := decided_a_data.source.epoch,
                                        target_epoch := decided_a_data.target.epoch,
                                        signing_root := Some(hash_tree_root(decided_a_data)));
        assert sdba in attestation_slashing_db';     

        assert !is_slashable_attestation_data(attestation_slashing_db', a'.data);

        var sdba' := SlashingDBAttestation(
                                        source_epoch := a'.data.source.epoch,
                                        target_epoch := a'.data.target.epoch,
                                        signing_root := None);        

        lemma_is_slashable_attestation_data(attestation_slashing_db', a'.data, sdba', sdba);
        assert !is_slashable_attestation_data_eth_spec(a.data, a'.data);
        assert !is_slashable_attestation_data_eth_spec(a'.data, a.data);
        
    }    

    lemma lemma_4_1_b(dvn: DVState, a: Attestation, a': Attestation, hn: BLSPubkey, hn': BLSPubkey)
    requires |dvn.all_nodes| > 0
    requires pred_4_1_b(dvn)
    requires pred_4_1_c(dvn)
    requires pred_4_1_f_a(dvn)
    requires inv42(dvn)
    requires pred_4_1_g_a(dvn)
    requires pred_4_1_g_b(dvn)
    requires hn in dvn.honest_nodes_states.Keys 
    requires hn' in dvn.honest_nodes_states.Keys
    requires a in dvn.honest_nodes_states[hn].bn.attestations_submitted
    requires a' in dvn.honest_nodes_states[hn'].bn.attestations_submitted
    requires a.data.slot == a'.data.slot 
    requires isConditionForSafetyTrue(dvn.consensus_on_attestation_data[a.data.slot])
    requires isConditionForSafetyTrue(dvn.consensus_on_attestation_data[a'.data.slot])
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
    requires pred_4_1_b(dvn)
    requires pred_4_1_c(dvn)
    requires pred_4_1_f_a(dvn)
    requires inv42(dvn)
    requires pred_4_1_g_a(dvn)
    requires pred_4_1_g_b(dvn)
    requires hn in dvn.honest_nodes_states.Keys 
    requires hn' in dvn.honest_nodes_states.Keys
    requires a in dvn.honest_nodes_states[hn].bn.attestations_submitted
    requires a' in dvn.honest_nodes_states[hn'].bn.attestations_submitted
    requires isConditionForSafetyTrue(dvn.consensus_on_attestation_data[a.data.slot])
    requires isConditionForSafetyTrue(dvn.consensus_on_attestation_data[a'.data.slot])
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
            
                    
        // TODO: Prove 4 g - i with lemma_decided_value_is_not_slashable_with_slashing_db_that_constructed_vp
        // and invariants 43--45.


    lemma lemma_decided_value_is_not_slashable_with_slashing_db_that_constructed_vp(
        dvn: DVState, 
        hn: BLSPubkey, 
        s: Slot,
        att: SlashingDBAttestation)
    requires inv43_body.requires(dvn, hn, s)    
    requires inv43_body(dvn, hn, s)    
    requires att in dvn.honest_nodes_states[hn].att_slashing_db_hist[s]
    requires dvn.consensus_on_attestation_data[s].decided_value.isPresent()
    ensures && var att_data := dvn.consensus_on_attestation_data[s].decided_value.safe_get();
            && var newRecord := construct_SlashingDBAttestation_from_att_data(att_data);
            && forall dbRecord | dbRecord in dvn.honest_nodes_states[hn].attestation_slashing_db ::
                    && !is_slashable_attestation_pair(dbRecord, newRecord)
                    && !is_slashable_attestation_pair(newRecord, dbRecord)

    


}