include "../../../common/commons.dfy"
include "attestation_creation_instrumented.dfy"
include "../../../specs/dvc/dvc_attestation_creation.dfy"
include "../../../specs/consensus/consensus.dfy"
include "../../../specs/network/network.dfy"
include "../../../specs/dv/dv_attestation_creation.dfy"
include "../supporting_lemmas/inv.dfy"
include "../../common/helper_sets_lemmas.dfy"
include "dvc_spec_axioms.dfy"


module Common_Proofs
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Helper_Sets_Lemmas
    import opened DVC_Spec_Axioms
    import DVC_Spec_NonInstr

    // TODO: Moved from invs_dv_next_3.dfy
    lemma lem_updateConsensusInstanceValidityCheck(
        s: ConsensusEngineState,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        r: ConsensusEngineState
    )
    requires r == updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db)        
    ensures r.att_slashing_db_hist.Keys
                == s.att_slashing_db_hist.Keys + s.active_attestation_consensus_instances.Keys
    {
        var new_active_attestation_consensus_instances := updateConsensusInstanceValidityCheckHelper(
                    s.active_attestation_consensus_instances,
                    new_attestation_slashing_db
                );

        lem_updateConsensusInstanceValidityCheckHelper(
                s.active_attestation_consensus_instances,
                new_attestation_slashing_db,
                new_active_attestation_consensus_instances);

        assert new_active_attestation_consensus_instances.Keys == s.active_attestation_consensus_instances.Keys;

        var new_att_slashing_db_hist := updateAttSlashingDBHist(
                                            s.att_slashing_db_hist,
                                            new_active_attestation_consensus_instances,
                                            new_attestation_slashing_db
                                        );

        assert new_att_slashing_db_hist.Keys 
                    == s.att_slashing_db_hist.Keys + new_active_attestation_consensus_instances.Keys;

        var t := s.(active_attestation_consensus_instances := new_active_attestation_consensus_instances,
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
            s.att_slashing_db_hist.Keys + new_active_attestation_consensus_instances.Keys;
            ==
            s.att_slashing_db_hist.Keys + s.active_attestation_consensus_instances.Keys;
        }
    }

    // TODO: Moved from invs_dv_next_3.dfy
    lemma lem_updateConsensusInstanceValidityCheckHelper(
        m: map<Slot, AttestationConsensusValidityCheckState>,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        m': map<Slot, AttestationConsensusValidityCheckState>
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

    lemma lem_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_updateAttSlashingDBHist(
        hist: map<Slot, map<AttestationData -> bool, set<set<SlashingDBAttestation>>>>,
        new_active_attestation_consensus_instances : map<Slot, AttestationConsensusValidityCheckState>,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        new_hist: map<Slot, map<AttestationData -> bool, set<set<SlashingDBAttestation>>>>
    )    
    requires new_hist == updateAttSlashingDBHist(hist, 
                                                 new_active_attestation_consensus_instances, 
                                                 new_attestation_slashing_db)
    ensures ( forall k: Slot | k in new_hist.Keys ::
                && ( k in new_active_attestation_consensus_instances.Keys
                        ==> && var vp := new_active_attestation_consensus_instances[k].validityPredicate;
                            && var hist_k := getOrDefault(hist, k, map[]);
                            && var hist_k_vp := getOrDefault(hist_k, vp, {}) + {new_attestation_slashing_db};
                            && new_hist[k][vp] == hist_k_vp                        
                   )
                && ( k !in new_active_attestation_consensus_instances.Keys
                        ==> new_hist[k] == hist[k]
                   )
            )
    { }

    lemma lem_inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_updateConsensusInstanceValidityCheck(
        s: ConsensusEngineState,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        r: ConsensusEngineState
    )
    requires r == updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db)        
    requires inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body_ces(s)
    requires ( forall k: Slot | k in s.active_attestation_consensus_instances.Keys ::
                    s.active_attestation_consensus_instances[k].attestation_duty.slot == k )
    ensures inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body_ces(r)
    {
        lem_updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db, r);
        assert r.att_slashing_db_hist.Keys
                == s.att_slashing_db_hist.Keys + s.active_attestation_consensus_instances.Keys;

        var new_active_attestation_consensus_instances := updateConsensusInstanceValidityCheckHelper(
                    s.active_attestation_consensus_instances,
                    new_attestation_slashing_db
                );

        assert forall k: Slot | k in new_active_attestation_consensus_instances.Keys ::
                    && var ci := new_active_attestation_consensus_instances[k];
                    && ci.validityPredicate
                        == ((ad: AttestationData) => consensus_is_valid_attestation_data(
                                                        new_attestation_slashing_db, 
                                                        ad, 
                                                        ci.attestation_duty)
                           );
                 
        



        var new_att_slashing_db_hist := updateAttSlashingDBHist(
                                            s.att_slashing_db_hist,
                                            new_active_attestation_consensus_instances,
                                            new_attestation_slashing_db
                                        );
        assert forall k: Slot | k in new_active_attestation_consensus_instances.Keys ::
                    && var ci := new_active_attestation_consensus_instances[k];
                    && var vp := ci.validityPredicate;
                    && var duty := ci.attestation_duty;
                    && duty.slot == k
                    && new_attestation_slashing_db in new_att_slashing_db_hist[k][vp]
                ;
        assert new_att_slashing_db_hist.Keys 
                    == s.att_slashing_db_hist.Keys + new_active_attestation_consensus_instances.Keys
                ;
        assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body_ces(s);

        forall k: Slot, vp: AttestationData -> bool | ( && k in new_att_slashing_db_hist.Keys
                                                        && vp in new_att_slashing_db_hist[k]
                                                      )
        ensures ( exists db: set<SlashingDBAttestation>, duty: AttestationDuty ::
                            && duty.slot == k
                            && db in new_att_slashing_db_hist[k][vp]
                            && vp == (ad: AttestationData) => consensus_is_valid_attestation_data(db, ad, duty)
                        )
        {
            if k in new_active_attestation_consensus_instances.Keys
            {
                var ci := new_active_attestation_consensus_instances[k];                

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
     
        lem_updateConsensusInstanceValidityCheckHelper(
                s.active_attestation_consensus_instances,
                new_attestation_slashing_db,
                new_active_attestation_consensus_instances);
        assert new_active_attestation_consensus_instances.Keys == s.active_attestation_consensus_instances.Keys;

        var t := s.(active_attestation_consensus_instances := new_active_attestation_consensus_instances,
                    att_slashing_db_hist := new_att_slashing_db_hist
                   );
        assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body_ces(t);
        assert r.att_slashing_db_hist.Keys == t.att_slashing_db_hist.Keys;
        assert inv_exists_db_in_att_slashing_db_hist_for_every_validity_pred_body_ces(r);
    }

    lemma lem_inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_updateConsensusInstanceValidityCheck(
        s: ConsensusEngineState,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        r: ConsensusEngineState
    )
    requires r == updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db)        
    requires inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(s, new_attestation_slashing_db)
    requires ( forall k: Slot | k in s.active_attestation_consensus_instances.Keys ::
                    s.active_attestation_consensus_instances[k].attestation_duty.slot == k )
    ensures inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(r, new_attestation_slashing_db)
    {
        lem_updateConsensusInstanceValidityCheck(s, new_attestation_slashing_db, r);
        assert r.att_slashing_db_hist.Keys
                == s.att_slashing_db_hist.Keys + s.active_attestation_consensus_instances.Keys;

        var new_active_attestation_consensus_instances := updateConsensusInstanceValidityCheckHelper(
                    s.active_attestation_consensus_instances,
                    new_attestation_slashing_db
                );

        assert forall k: Slot | k in new_active_attestation_consensus_instances.Keys ::
                    && var ci := new_active_attestation_consensus_instances[k];
                    && ci.validityPredicate
                        == ((ad: AttestationData) => consensus_is_valid_attestation_data(
                                                        new_attestation_slashing_db, 
                                                        ad, 
                                                        ci.attestation_duty)
                           );
                 
        var new_att_slashing_db_hist := updateAttSlashingDBHist(
                                            s.att_slashing_db_hist,
                                            new_active_attestation_consensus_instances,
                                            new_attestation_slashing_db
                                        );
        assert forall k: Slot | k in new_active_attestation_consensus_instances.Keys ::
                    && var ci := new_active_attestation_consensus_instances[k];
                    && var vp := ci.validityPredicate;
                    && var duty := ci.attestation_duty;
                    && duty.slot == k
                    && new_attestation_slashing_db in new_att_slashing_db_hist[k][vp]
                ;
        assert forall k: Slot, vp, db | 
                    && k in new_active_attestation_consensus_instances.Keys 
                    && vp in new_att_slashing_db_hist[k]
                    && db in new_att_slashing_db_hist[k][vp]
                    ::
                    && db <= new_attestation_slashing_db 
                ;
        assert new_att_slashing_db_hist.Keys 
                    == s.att_slashing_db_hist.Keys + new_active_attestation_consensus_instances.Keys
                ;
        assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(s, new_attestation_slashing_db);

        forall k: Slot, vp: AttestationData -> bool, db | 
                    ( && k in new_att_slashing_db_hist.Keys
                      && vp in new_att_slashing_db_hist[k]
                      && db in new_att_slashing_db_hist[k][vp]
                    )
        ensures db <= new_attestation_slashing_db
        {
            if k in new_active_attestation_consensus_instances.Keys
            {
                var ci := new_active_attestation_consensus_instances[k];                

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
     
        var t := s.(active_attestation_consensus_instances := new_active_attestation_consensus_instances,
                    att_slashing_db_hist := new_att_slashing_db_hist
                   );
        assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(t, new_attestation_slashing_db);
        assert r.att_slashing_db_hist.Keys == t.att_slashing_db_hist.Keys;
        assert inv_every_db_in_att_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(r, new_attestation_slashing_db);
    }
}