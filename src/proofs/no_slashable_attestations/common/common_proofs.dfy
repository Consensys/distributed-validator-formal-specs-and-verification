include "../../../common/commons.dfy"
include "dvc_attestation_creation_instrumented.dfy"
include "../../../specs/dvc/dvc_attestation_creation.dfy"
include "../../../specs/consensus/consensus.dfy"
include "../../../specs/network/network.dfy"
include "../../../specs/dv/dv_attestation_creation.dfy"
include "../supporting_lemmas/inv.dfy"
include "../../bn_axioms.dfy"
include "../../rs_axioms.dfy"


module Common_Proofs
{
    import opened Types 
    import opened Common_Functions
    import opened Set_Seq_Helper
    import opened Signing_Methods
    import opened Consensus
    import opened Consensus_Engine
    import opened Network_Spec
    import opened Att_DVC
    import opened Att_DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened BN_Axioms
    import opened RS_Axioms
    import Non_Instr_Att_DVC

    lemma lem_f_update_att_consensus_engine_state(
        s: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        r: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>
    )
    requires r == f_update_att_consensus_engine_state(s, new_attestation_slashing_db)        
    ensures r.slashing_db_hist.Keys
                == s.slashing_db_hist.Keys + s.active_consensus_instances.Keys
    {
        var new_active_consensus_instances := f_update_att_consensus_instance_validity_check_states(
                    s.active_consensus_instances,
                    new_attestation_slashing_db
                );

        lem_f_update_att_consensus_instance_validity_check_states(
                s.active_consensus_instances,
                new_attestation_slashing_db,
                new_active_consensus_instances);

        assert new_active_consensus_instances.Keys == s.active_consensus_instances.Keys;

        var new_slashing_db_hist := f_update_att_slashing_db_hist_with_new_consensus_instances_and_slashing_db_attestations(
                                            s.slashing_db_hist,
                                            new_active_consensus_instances,
                                            new_attestation_slashing_db
                                        );

        assert new_slashing_db_hist.Keys 
                    == s.slashing_db_hist.Keys + new_active_consensus_instances.Keys;

        var t := s.(active_consensus_instances := new_active_consensus_instances,
                    slashing_db_hist := new_slashing_db_hist
                   );

        assert r.slashing_db_hist.Keys == t.slashing_db_hist.Keys;

        calc 
        {
            r.slashing_db_hist.Keys;
            ==
            t.slashing_db_hist.Keys;
            ==
            new_slashing_db_hist.Keys;
            == 
            s.slashing_db_hist.Keys + new_active_consensus_instances.Keys;
            ==
            s.slashing_db_hist.Keys + s.active_consensus_instances.Keys;
        }
    }

    lemma lem_f_update_att_consensus_instance_validity_check_states(
        m: map<Slot, AttestationConsensusValidityCheckState>,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        m': map<Slot, AttestationConsensusValidityCheckState>
    )    
    requires m' == f_update_att_consensus_instance_validity_check_states(m, new_attestation_slashing_db)
    ensures m.Keys == m'.Keys
    ensures forall slot |
                && slot in m'.Keys 
                ::
                var acvc := m'[slot];
                && acvc.validityPredicate == ((ad: AttestationData) => ci_decision_att_signature_is_signed_with_pubkey_data(new_attestation_slashing_db, ad, acvc.attestation_duty));
  
    {
        forall k | k in  m 
        ensures k in m'
        {
            lem_map_keys_has_one_entry_in_items(m, k);
            assert k in m';
        }

        assert m.Keys == m'.Keys;

        assert forall slot |
                && slot in m'.Keys 
                ::
                var acvc := m'[slot];
                && acvc.validityPredicate == (ad: AttestationData) => ci_decision_att_signature_is_signed_with_pubkey_data(new_attestation_slashing_db, ad, acvc.attestation_duty);

    }  

    lemma lem_inv_exist_db_in_slashing_db_hist_and_att_duty_for_every_validity_predicate_f_update_att_slashing_db_hist_with_new_consensus_instances_and_slashing_db_attestations(
        hist: map<Slot, map<AttestationData -> bool, set<set<SlashingDBAttestation>>>>,
        new_active_consensus_instances : map<Slot, AttestationConsensusValidityCheckState>,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        new_hist: map<Slot, map<AttestationData -> bool, set<set<SlashingDBAttestation>>>>
    )    
    requires new_hist == f_update_att_slashing_db_hist_with_new_consensus_instances_and_slashing_db_attestations(hist, 
                                                 new_active_consensus_instances, 
                                                 new_attestation_slashing_db)
    ensures ( forall k: Slot | k in new_hist.Keys ::
                && ( (k in new_active_consensus_instances.Keys)
                        ==> ( && var vp := new_active_consensus_instances[k].validityPredicate;
                              && var hist_k := get_or_default(hist, k, map[]);
                              && var hist_k_vp := get_or_default(hist_k, vp, {}) + {new_attestation_slashing_db};
                              && new_hist[k][vp] == hist_k_vp                        
                            )
                   )
                && ( (k !in new_active_consensus_instances.Keys)
                        ==> new_hist[k] == hist[k]
                   )
            )
    { }

    lemma lem_inv_exist_db_in_slashing_db_hist_and_att_duty_for_every_validity_predicate_f_update_att_consensus_engine_state(
        s: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        r: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>
    )
    requires r == f_update_att_consensus_engine_state(s, new_attestation_slashing_db)        
    requires inv_exist_db_in_slashing_db_hist_and_att_duty_for_every_validity_predicate_body_ces(s)
    requires ( forall k: Slot | k in s.active_consensus_instances.Keys ::
                    s.active_consensus_instances[k].attestation_duty.slot == k )
    ensures inv_exist_db_in_slashing_db_hist_and_att_duty_for_every_validity_predicate_body_ces(r)
    {
        lem_f_update_att_consensus_engine_state(s, new_attestation_slashing_db, r);
        assert r.slashing_db_hist.Keys
                == s.slashing_db_hist.Keys + s.active_consensus_instances.Keys;

        var new_active_consensus_instances := f_update_att_consensus_instance_validity_check_states(
                    s.active_consensus_instances,
                    new_attestation_slashing_db
                );

        assert forall k: Slot | k in new_active_consensus_instances.Keys ::
                    && var ci := new_active_consensus_instances[k];
                    && ci.validityPredicate
                        == ((ad: AttestationData) => ci_decision_att_signature_is_signed_with_pubkey_data(
                                                        new_attestation_slashing_db, 
                                                        ad, 
                                                        ci.attestation_duty)
                           );
                 
        



        var new_slashing_db_hist := f_update_att_slashing_db_hist_with_new_consensus_instances_and_slashing_db_attestations(
                                            s.slashing_db_hist,
                                            new_active_consensus_instances,
                                            new_attestation_slashing_db
                                        );
        assert forall k: Slot | k in new_active_consensus_instances.Keys ::
                    && var ci := new_active_consensus_instances[k];
                    && var vp := ci.validityPredicate;
                    && var duty := ci.attestation_duty;
                    && duty.slot == k
                    && new_attestation_slashing_db in new_slashing_db_hist[k][vp]
                ;
        assert new_slashing_db_hist.Keys 
                    == s.slashing_db_hist.Keys + new_active_consensus_instances.Keys
                ;
        assert inv_exist_db_in_slashing_db_hist_and_att_duty_for_every_validity_predicate_body_ces(s);

        forall k: Slot, vp: AttestationData -> bool | ( && k in new_slashing_db_hist.Keys
                                                        && vp in new_slashing_db_hist[k]
                                                      )
        ensures ( exists db: set<SlashingDBAttestation>, duty: AttestationDuty ::
                            && duty.slot == k
                            && db in new_slashing_db_hist[k][vp]
                            && vp == (ad: AttestationData) => ci_decision_att_signature_is_signed_with_pubkey_data(db, ad, duty)
                        )
        {
            if k in new_active_consensus_instances.Keys
            {
                var ci := new_active_consensus_instances[k];                

                if vp == ci.validityPredicate
                {
                    var duty := ci.attestation_duty;
                    assert  && duty.slot == k
                            && new_attestation_slashing_db in new_slashing_db_hist[k][vp];
                    assert (exists db: set<SlashingDBAttestation>, duty: AttestationDuty ::
                            && duty.slot == k
                            && db in new_slashing_db_hist[k][vp]
                            && vp == (ad: AttestationData) => ci_decision_att_signature_is_signed_with_pubkey_data(db, ad, duty)
                        );
                }
                else 
                {
                    assert vp in s.slashing_db_hist[k];
                    assert (exists db: set<SlashingDBAttestation>, duty: AttestationDuty ::
                            && duty.slot == k
                            && db in s.slashing_db_hist[k][vp]
                            && vp == (ad: AttestationData) => ci_decision_att_signature_is_signed_with_pubkey_data(db, ad, duty)
                        );
                }
            }
            else
            {                
                assert k in s.slashing_db_hist.Keys;
                assert vp in s.slashing_db_hist[k];
                assert (exists db: set<SlashingDBAttestation>, duty: AttestationDuty ::
                            && duty.slot == k
                            && db in s.slashing_db_hist[k][vp]
                            && vp == (ad: AttestationData) => ci_decision_att_signature_is_signed_with_pubkey_data(db, ad, duty)
                        );                
            }
        }
     
        lem_f_update_att_consensus_instance_validity_check_states(
                s.active_consensus_instances,
                new_attestation_slashing_db,
                new_active_consensus_instances);
        assert new_active_consensus_instances.Keys == s.active_consensus_instances.Keys;

        var t := s.(active_consensus_instances := new_active_consensus_instances,
                    slashing_db_hist := new_slashing_db_hist
                   );
        assert inv_exist_db_in_slashing_db_hist_and_att_duty_for_every_validity_predicate_body_ces(t);
        assert r.slashing_db_hist.Keys == t.slashing_db_hist.Keys;
        assert inv_exist_db_in_slashing_db_hist_and_att_duty_for_every_validity_predicate_body_ces(r);
    }

    lemma lem_inv_every_db_in_slashing_db_hist_is_subset_of_att_slashing_db_body_f_update_att_consensus_engine_state(
        s: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>,
        new_attestation_slashing_db: set<SlashingDBAttestation>,
        r: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>
    )
    requires r == f_update_att_consensus_engine_state(s, new_attestation_slashing_db)        
    requires inv_every_db_in_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(s, new_attestation_slashing_db)
    requires ( forall k: Slot | k in s.active_consensus_instances.Keys ::
                    s.active_consensus_instances[k].attestation_duty.slot == k )
    ensures inv_every_db_in_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(r, new_attestation_slashing_db)
    {
        lem_f_update_att_consensus_engine_state(s, new_attestation_slashing_db, r);
        assert r.slashing_db_hist.Keys
                == s.slashing_db_hist.Keys + s.active_consensus_instances.Keys;

        var new_active_consensus_instances := f_update_att_consensus_instance_validity_check_states(
                    s.active_consensus_instances,
                    new_attestation_slashing_db
                );

        assert forall k: Slot | k in new_active_consensus_instances.Keys ::
                    && var ci := new_active_consensus_instances[k];
                    && ci.validityPredicate
                        == ((ad: AttestationData) => ci_decision_att_signature_is_signed_with_pubkey_data(
                                                        new_attestation_slashing_db, 
                                                        ad, 
                                                        ci.attestation_duty)
                           );
                 
        var new_slashing_db_hist := f_update_att_slashing_db_hist_with_new_consensus_instances_and_slashing_db_attestations(
                                            s.slashing_db_hist,
                                            new_active_consensus_instances,
                                            new_attestation_slashing_db
                                        );
        assert forall k: Slot | k in new_active_consensus_instances.Keys ::
                    && var ci := new_active_consensus_instances[k];
                    && var vp := ci.validityPredicate;
                    && var duty := ci.attestation_duty;
                    && duty.slot == k
                    && new_attestation_slashing_db in new_slashing_db_hist[k][vp]
                ;
        assert forall k: Slot, vp, db | 
                    && k in new_active_consensus_instances.Keys 
                    && vp in new_slashing_db_hist[k]
                    && db in new_slashing_db_hist[k][vp]
                    ::
                    && db <= new_attestation_slashing_db 
                ;
        assert new_slashing_db_hist.Keys 
                    == s.slashing_db_hist.Keys + new_active_consensus_instances.Keys
                ;
        assert inv_every_db_in_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(s, new_attestation_slashing_db);

        forall k: Slot, vp: AttestationData -> bool, db | 
                    ( && k in new_slashing_db_hist.Keys
                      && vp in new_slashing_db_hist[k]
                      && db in new_slashing_db_hist[k][vp]
                    )
        ensures db <= new_attestation_slashing_db
        {
            if k in new_active_consensus_instances.Keys
            {
                var ci := new_active_consensus_instances[k];                

                if vp == ci.validityPredicate
                {
                    assert db <= new_attestation_slashing_db;                    
                }
                else 
                {
                    assert vp in s.slashing_db_hist[k];
                    assert db <= new_attestation_slashing_db;                        
                }
            }
            else
            {                
                assert k in s.slashing_db_hist.Keys;
                assert vp in s.slashing_db_hist[k];
                assert db <= new_attestation_slashing_db;                
            }
        }
     
        var t := s.(active_consensus_instances := new_active_consensus_instances,
                    slashing_db_hist := new_slashing_db_hist
                   );
        assert inv_every_db_in_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(t, new_attestation_slashing_db);
        assert r.slashing_db_hist.Keys == t.slashing_db_hist.Keys;
        assert inv_every_db_in_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(r, new_attestation_slashing_db);
    }    
}