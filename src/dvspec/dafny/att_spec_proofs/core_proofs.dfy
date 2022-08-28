include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"

module Core_Proofs
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened AttInvariants

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
    
    lemma  lem_1(dvn: DVState)
    ensures safety(dvn)

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
                                    && is_slashable_attestation_data_in_set_of_attestations(tempSet, a.data);
            decreases |unchecked_attestations|
        {
            var a: Attestation :| a in unchecked_attestations;
            assert a in dvn.globally_signed_attestations;
            assert a in attestations;

            var tempSet := dvn.globally_signed_attestations - { a };
            assert tempSet <= attestations;

            assert is_slashable_attestation_data_in_set_of_attestations(tempSet, a.data);

            unchecked_attestations := unchecked_attestations - { a };   
            checked_attestations := checked_attestations + { a };
        }
        

        assert checked_attestations == dvn.globally_signed_attestations;
        assert forall a: Attestation :: 
                    a in dvn.globally_signed_attestations
                        ==> && var tempSet := dvn.globally_signed_attestations - { a };
                            && is_slashable_attestation_data_in_set_of_attestations(tempSet, a.data);
    }
}