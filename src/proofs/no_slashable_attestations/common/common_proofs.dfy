include "../../../common/commons.dfy"
include "attestation_creation_instrumented.dfy"
include "../../../specs/dvc/attestation_creation.dfy"
include "../../../specs/consensus/consensus.dfy"
include "../../../specs/network/network.dfy"
include "../../../specs/dvn/dvn.dfy"
include "../supporting_lemmas/inv.dfy"
include "../../common/helper_sets_lemmas.dfy"
include "dvc_spec_axioms.dfy"


module Common_Proofs
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Helper_Sets_Lemmas
    import opened DVCNode_Spec_Axioms
    import DVCNode_Spec_NonInstr

    // TODO: Moved from ind_inv.dfy
    lemma lemma_updateConsensusInstanceValidityCheck(
        s: ConsensusEngineState,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        r: ConsensusEngineState
    )
    requires r == updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db)        
    ensures r.att_slashing_db_hist.Keys
                == s.att_slashing_db_hist.Keys + s.attestation_consensus_active_instances.Keys
    {
        var new_attestation_consensus_active_instances := updateConsensusInstanceValidityCheckHelper(
                    s.attestation_consensus_active_instances,
                    new_attestation_slashing_db
                );

        lemma_updateConsensusInstanceValidityCheckHelper(
                s.attestation_consensus_active_instances,
                new_attestation_slashing_db,
                new_attestation_consensus_active_instances);

        assert new_attestation_consensus_active_instances.Keys == s.attestation_consensus_active_instances.Keys;

        var new_att_slashing_db_hist := updateAttSlashingDBHist(
                                            s.att_slashing_db_hist,
                                            new_attestation_consensus_active_instances,
                                            new_attestation_slashing_db
                                        );

        assert new_att_slashing_db_hist.Keys 
                    == s.att_slashing_db_hist.Keys + new_attestation_consensus_active_instances.Keys;

        var t := s.(attestation_consensus_active_instances := new_attestation_consensus_active_instances,
                    att_slashing_db_hist := new_att_slashing_db_hist
                   );

        assert r.att_slashing_db_hist.Keys == t.att_slashing_db_hist.Keys;

        calc 
        {
            r.att_slashing_db_hist.Keys;
            ==
            t.att_slashing_db_hist.Keys;
            ==
            new_att_slashing_db_hist.Keys;
            == 
            s.att_slashing_db_hist.Keys + new_attestation_consensus_active_instances.Keys;
            ==
            s.att_slashing_db_hist.Keys + s.attestation_consensus_active_instances.Keys;
        }
    }

    // TODO: Moved from ind_inv.dfy
    lemma lemma_updateConsensusInstanceValidityCheckHelper(
        m: map<Slot, DVCNode_Spec_NonInstr.AttestationConsensusValidityCheckState>,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        m': map<Slot, DVCNode_Spec_NonInstr.AttestationConsensusValidityCheckState>
    )    
    requires m' == updateConsensusInstanceValidityCheckHelper(m, new_attestation_slashing_db)
    ensures m.Keys == m'.Keys
    ensures forall slot |
                && slot in m'.Keys 
                ::
                var acvc := m'[slot];
                && acvc.validityPredicate == ((ad: AttestationData) => consensus_is_valid_attestation_data(new_attestation_slashing_db, ad, acvc.attestation_duty));
  
    {
        forall k | k in  m 
        ensures k in m'
        {
            lemmaMapKeysHasOneEntryInItems(m, k);
            assert k in m';
        }

        assert m.Keys == m'.Keys;

        assert forall slot |
                && slot in m'.Keys 
                ::
                var acvc := m'[slot];
                && acvc.validityPredicate == (ad: AttestationData) => consensus_is_valid_attestation_data(new_attestation_slashing_db, ad, acvc.attestation_duty);

    }  

    lemma lemma_inv28_updateAttSlashingDBHist(
        hist: map<Slot, map<AttestationData -> bool, set<set<SlashingDBAttestation>>>>,
        new_attestation_consensus_active_instances : map<Slot, DVCNode_Spec_NonInstr.AttestationConsensusValidityCheckState>,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        new_hist: map<Slot, map<AttestationData -> bool, set<set<SlashingDBAttestation>>>>
    )    
    requires new_hist == updateAttSlashingDBHist(hist, 
                                                 new_attestation_consensus_active_instances, 
                                                 new_attestation_slashing_db)
    ensures ( forall k: Slot | k in new_hist.Keys ::
                && ( k in new_attestation_consensus_active_instances.Keys
                        ==> && var vp := new_attestation_consensus_active_instances[k].validityPredicate;
                            && var hist_k := getOrDefault(hist, k, map[]);
                            && var hist_k_vp := getOrDefault(hist_k, vp, {}) + {new_attestation_slashing_db};
                            && new_hist[k][vp] == hist_k_vp                        
                   )
                && ( k !in new_attestation_consensus_active_instances.Keys
                        ==> new_hist[k] == hist[k]
                   )
            )
    { }

    lemma lemma_inv28_updateConsensusInstanceValidityCheck(
        s: ConsensusEngineState,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        r: ConsensusEngineState
    )
    requires r == updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db)        
    requires inv28_body_ces(s)
    requires ( forall k: Slot | k in s.attestation_consensus_active_instances.Keys ::
                    s.attestation_consensus_active_instances[k].attestation_duty.slot == k )
    ensures inv28_body_ces(r)
    {
        lemma_updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db, r);
        assert r.att_slashing_db_hist.Keys
                == s.att_slashing_db_hist.Keys + s.attestation_consensus_active_instances.Keys;

        var new_attestation_consensus_active_instances := updateConsensusInstanceValidityCheckHelper(
                    s.attestation_consensus_active_instances,
                    new_attestation_slashing_db
                );

        assert forall k: Slot | k in new_attestation_consensus_active_instances.Keys ::
                    && var ci := new_attestation_consensus_active_instances[k];
                    && ci.validityPredicate
                        == ((ad: AttestationData) => consensus_is_valid_attestation_data(
                                                        new_attestation_slashing_db, 
                                                        ad, 
                                                        ci.attestation_duty)
                           );
                 
        



        var new_att_slashing_db_hist := updateAttSlashingDBHist(
                                            s.att_slashing_db_hist,
                                            new_attestation_consensus_active_instances,
                                            new_attestation_slashing_db
                                        );
        assert forall k: Slot | k in new_attestation_consensus_active_instances.Keys ::
                    && var ci := new_attestation_consensus_active_instances[k];
                    && var vp := ci.validityPredicate;
                    && var duty := ci.attestation_duty;
                    && duty.slot == k
                    && new_attestation_slashing_db in new_att_slashing_db_hist[k][vp]
                ;
        assert new_att_slashing_db_hist.Keys 
                    == s.att_slashing_db_hist.Keys + new_attestation_consensus_active_instances.Keys
                ;
        assert inv28_body_ces(s);

        forall k: Slot, vp: AttestationData -> bool | ( && k in new_att_slashing_db_hist.Keys
                                                        && vp in new_att_slashing_db_hist[k]
                                                      )
        ensures ( exists db: set<SlashingDBAttestation>, duty: AttestationDuty ::
                            && duty.slot == k
                            && db in new_att_slashing_db_hist[k][vp]
                            && vp == (ad: AttestationData) => consensus_is_valid_attestation_data(db, ad, duty)
                        )
        {
            if k in new_attestation_consensus_active_instances.Keys
            {
                var ci := new_attestation_consensus_active_instances[k];                

                if vp == ci.validityPredicate
                {
                    var duty := ci.attestation_duty;
                    assert  && duty.slot == k
                            && new_attestation_slashing_db in new_att_slashing_db_hist[k][vp];
                    assert (exists db: set<SlashingDBAttestation>, duty: AttestationDuty ::
                            && duty.slot == k
                            && db in new_att_slashing_db_hist[k][vp]
                            && vp == (ad: AttestationData) => consensus_is_valid_attestation_data(db, ad, duty)
                        );
                }
                else 
                {
                    assert vp in s.att_slashing_db_hist[k];
                    assert (exists db: set<SlashingDBAttestation>, duty: AttestationDuty ::
                            && duty.slot == k
                            && db in s.att_slashing_db_hist[k][vp]
                            && vp == (ad: AttestationData) => consensus_is_valid_attestation_data(db, ad, duty)
                        );
                }
            }
            else
            {                
                assert k in s.att_slashing_db_hist.Keys;
                assert vp in s.att_slashing_db_hist[k];
                assert (exists db: set<SlashingDBAttestation>, duty: AttestationDuty ::
                            && duty.slot == k
                            && db in s.att_slashing_db_hist[k][vp]
                            && vp == (ad: AttestationData) => consensus_is_valid_attestation_data(db, ad, duty)
                        );                
            }
        }
     
        lemma_updateConsensusInstanceValidityCheckHelper(
                s.attestation_consensus_active_instances,
                new_attestation_slashing_db,
                new_attestation_consensus_active_instances);
        assert new_attestation_consensus_active_instances.Keys == s.attestation_consensus_active_instances.Keys;

        var t := s.(attestation_consensus_active_instances := new_attestation_consensus_active_instances,
                    att_slashing_db_hist := new_att_slashing_db_hist
                   );
        assert inv28_body_ces(t);
        assert r.att_slashing_db_hist.Keys == t.att_slashing_db_hist.Keys;
        assert inv28_body_ces(r);
    }

    lemma lemma_inv31_updateConsensusInstanceValidityCheck(
        s: ConsensusEngineState,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        r: ConsensusEngineState
    )
    requires r == updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db)        
    requires inv31_body_ces(s, new_attestation_slashing_db)
    requires ( forall k: Slot | k in s.attestation_consensus_active_instances.Keys ::
                    s.attestation_consensus_active_instances[k].attestation_duty.slot == k )
    ensures inv31_body_ces(r, new_attestation_slashing_db)
    {
        lemma_updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db, r);
        assert r.att_slashing_db_hist.Keys
                == s.att_slashing_db_hist.Keys + s.attestation_consensus_active_instances.Keys;

        var new_attestation_consensus_active_instances := updateConsensusInstanceValidityCheckHelper(
                    s.attestation_consensus_active_instances,
                    new_attestation_slashing_db
                );

        assert forall k: Slot | k in new_attestation_consensus_active_instances.Keys ::
                    && var ci := new_attestation_consensus_active_instances[k];
                    && ci.validityPredicate
                        == ((ad: AttestationData) => consensus_is_valid_attestation_data(
                                                        new_attestation_slashing_db, 
                                                        ad, 
                                                        ci.attestation_duty)
                           );
                 
        var new_att_slashing_db_hist := updateAttSlashingDBHist(
                                            s.att_slashing_db_hist,
                                            new_attestation_consensus_active_instances,
                                            new_attestation_slashing_db
                                        );
        assert forall k: Slot | k in new_attestation_consensus_active_instances.Keys ::
                    && var ci := new_attestation_consensus_active_instances[k];
                    && var vp := ci.validityPredicate;
                    && var duty := ci.attestation_duty;
                    && duty.slot == k
                    && new_attestation_slashing_db in new_att_slashing_db_hist[k][vp]
                ;
        assert forall k: Slot, vp, db | 
                    && k in new_attestation_consensus_active_instances.Keys 
                    && vp in new_att_slashing_db_hist[k]
                    && db in new_att_slashing_db_hist[k][vp]
                    ::
                    && db <= new_attestation_slashing_db 
                ;
        assert new_att_slashing_db_hist.Keys 
                    == s.att_slashing_db_hist.Keys + new_attestation_consensus_active_instances.Keys
                ;
        assert inv31_body_ces(s, new_attestation_slashing_db);

        forall k: Slot, vp: AttestationData -> bool, db | 
                    ( && k in new_att_slashing_db_hist.Keys
                      && vp in new_att_slashing_db_hist[k]
                      && db in new_att_slashing_db_hist[k][vp]
                    )
        ensures db <= new_attestation_slashing_db
        {
            if k in new_attestation_consensus_active_instances.Keys
            {
                var ci := new_attestation_consensus_active_instances[k];                

                if vp == ci.validityPredicate
                {
                    assert db <= new_attestation_slashing_db;                    
                }
                else 
                {
                    assert vp in s.att_slashing_db_hist[k];
                    assert db <= new_attestation_slashing_db;                        
                }
            }
            else
            {                
                assert k in s.att_slashing_db_hist.Keys;
                assert vp in s.att_slashing_db_hist[k];
                assert db <= new_attestation_slashing_db;                
            }
        }
     
        var t := s.(attestation_consensus_active_instances := new_attestation_consensus_active_instances,
                    att_slashing_db_hist := new_att_slashing_db_hist
                   );
        assert inv31_body_ces(t, new_attestation_slashing_db);
        assert r.att_slashing_db_hist.Keys == t.att_slashing_db_hist.Keys;
        assert inv31_body_ces(r, new_attestation_slashing_db);
    }
}