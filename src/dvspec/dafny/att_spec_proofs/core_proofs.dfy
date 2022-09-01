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

    lemma lemma_4_1(dvn: DVState, a: Attestation, a': Attestation, hn: BLSPubkey, hn': BLSPubkey)
    requires pred_4_1_b(dvn)
    requires pred_4_1_c(dvn)
    requires pred_4_1_f_a(dvn)
    requires hn in dvn.honest_nodes_states.Keys 
    requires hn' in dvn.honest_nodes_states.Keys
    requires a in dvn.honest_nodes_states[hn].bn.attestations_submitted
    requires a' in dvn.honest_nodes_states[hn'].bn.attestations_submitted
    requires a.data.slot < a'.data.slot 
    // ensures   
    //         var sdba := SlashingDBAttestation(
    //                         source_epoch := a.data.source.epoch,
    //                         target_epoch := a.data.target.epoch,
    //                         signing_root := None
    //                 );   
    //         var sdba' := SlashingDBAttestation(
    //                         source_epoch := a'.data.source.epoch,
    //                         target_epoch := a'.data.target.epoch,
    //                         signing_root := None
    //                 );                       
    //         !is_slashable_attestation_pair(sdba, sdba')
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

        assert is_a_valid_decided_value(dvn.consensus_on_attestation_data[a.data.slot]); 
        assert is_a_valid_decided_value(dvn.consensus_on_attestation_data[a'.data.slot]);  

        var consa := dvn.consensus_on_attestation_data[a.data.slot]; 

        assert consa.decided_value.isPresent();

/*
        var h_nodes_a :|
                && h_nodes_a <= consa.honest_nodes_validity_functions.Keys  
                && |h_nodes_a| >= f(|consa.all_nodes|) + 1
                &&
                (forall n | n in h_nodes_a :: 
                    exists vp: AttestationData -> bool | vp in consa.honest_nodes_validity_functions[n] :: vp(consa.decided_value.safe_get()));                                   
                    */
    }


    lemma lemma_4_1_f_i(dvn: DVState, a: Attestation, a': Attestation, hn: BLSPubkey, hn': BLSPubkey)
    requires pred_4_1_b(dvn)
    requires pred_4_1_c(dvn)
    requires pred_4_1_f_a(dvn)
    requires hn in dvn.honest_nodes_states.Keys 
    requires hn' in dvn.honest_nodes_states.Keys
    requires a in dvn.honest_nodes_states[hn].bn.attestations_submitted
    requires a' in dvn.honest_nodes_states[hn'].bn.attestations_submitted
    requires a.data.slot < a'.data.slot 
    requires is_a_valid_decided_value(dvn.consensus_on_attestation_data[a.data.slot])
    requires is_a_valid_decided_value(dvn.consensus_on_attestation_data[a'.data.slot])
    requires dvn.consensus_on_attestation_data[a.data.slot].decided_value.isPresent()
    requires dvn.consensus_on_attestation_data[a'.data.slot].decided_value.isPresent()
    requires && inv41(dvn.consensus_on_attestation_data[a.data.slot])
             && isConditionForSafetyTrue(dvn.consensus_on_attestation_data[a.data.slot])
    requires && inv41(dvn.consensus_on_attestation_data[a'.data.slot])
             && isConditionForSafetyTrue(dvn.consensus_on_attestation_data[a'.data.slot])             
    requires inv42(dvn)
    requires |dvn.all_nodes| > 0
    // ensures   
    //         var sdba := SlashingDBAttestation(
    //                         source_epoch := a.data.source.epoch,
    //                         target_epoch := a.data.target.epoch,
    //                         signing_root := None
    //                 );   
    //         var sdba' := SlashingDBAttestation(
    //                         source_epoch := a'.data.source.epoch,
    //                         target_epoch := a'.data.target.epoch,
    //                         signing_root := None
    //                 );                       
    //         !is_slashable_attestation_pair(sdba, sdba')
    {
        var consa := dvn.consensus_on_attestation_data[a.data.slot];         
        var h_nodes_a :|
                && h_nodes_a <= consa.honest_nodes_validity_functions.Keys  
                && |h_nodes_a| >= quorum(|consa.all_nodes|) 
                                        - (|consa.all_nodes| - |consa.honest_nodes_status.Keys|)
                && honest_nodes_with_validityPredicate(consa, h_nodes_a);         

        var consa' := dvn.consensus_on_attestation_data[a'.data.slot];         
        var h_nodes_a' :|
                && h_nodes_a' <= consa'.honest_nodes_validity_functions.Keys  
                && |h_nodes_a'| >= quorum(|consa'.all_nodes|) 
                                        - (|consa'.all_nodes| - |consa'.honest_nodes_status.Keys|)
                && honest_nodes_with_validityPredicate(consa', h_nodes_a');    

        assert consa in dvn.consensus_on_attestation_data.Values;                    
        assert consa' in dvn.consensus_on_attestation_data.Values;
        assert consa.all_nodes == consa'.all_nodes == dvn.all_nodes;
        assert consa.honest_nodes_status.Keys == consa'.honest_nodes_status.Keys;   

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

        // TODO: 4g

    }
}