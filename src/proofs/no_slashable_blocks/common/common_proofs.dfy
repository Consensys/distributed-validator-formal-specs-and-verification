include "../../../common/block_proposer/block_types.dfy"
include "../../../common/block_proposer/block_common_functions.dfy"
include "../../../common/block_proposer/block_signing_functions.dfy"
include "dvc_block_proposer_instrumented.dfy"
include "../../../specs/consensus/block_consensus.dfy"
include "../../../specs/network/block_network.dfy"
include "../supporting_lemmas/inv.dfy"
include "../../common/helper_sets_lemmas.dfy"
include "block_dvc_spec_axioms.dfy"


module Common_Proofs_For_Block_Proposer
{
    import opened Block_Types 
    import opened Block_Common_Functions
    import opened Block_Consensus_Spec
    import opened Block_Network_Spec
    import opened DVC_Block_Proposer_Spec_Instr
    import opened DV_Block_Proposer_Spec
    import opened Block_Inv_With_Empty_Initial_Block_Slashing_DB
    import opened Helper_Sets_Lemmas
    import opened DVC_Block_Proposer_Spec_Axioms

    lemma lem_updateBlockConsensusInstanceValidityCheck(
        s: BlockConsensusEngineState,
        new_block_slashing_db: set<SlashingDBBlock>,        
        r: BlockConsensusEngineState
    )
    requires r == updateBlockConsensusInstanceValidityCheck(s, new_block_slashing_db)        
    ensures r.block_slashing_db_hist.Keys
                == s.block_slashing_db_hist.Keys + s.active_block_consensus_instances.Keys
    {
        var new_active_block_consensus_instances := updateBlockConsensusInstanceValidityCheckHelper(
                    s.active_block_consensus_instances,
                    new_block_slashing_db
                );

        lem_updateBlockConsensusInstanceValidityCheckHelper(
                s.active_block_consensus_instances,
                new_block_slashing_db,
                new_active_block_consensus_instances);

        assert new_active_block_consensus_instances.Keys == s.active_block_consensus_instances.Keys;

        var new_block_slashing_db_hist := updateBlockSlashingDBHist(
                                            s.block_slashing_db_hist,
                                            new_active_block_consensus_instances,
                                            new_block_slashing_db
                                        );

        assert new_block_slashing_db_hist.Keys 
                    == s.block_slashing_db_hist.Keys + new_active_block_consensus_instances.Keys;

        var t := s.(active_block_consensus_instances := new_active_block_consensus_instances,
                    block_slashing_db_hist := new_block_slashing_db_hist
                   );

        assert r.block_slashing_db_hist.Keys == t.block_slashing_db_hist.Keys;

        calc 
        {
            r.block_slashing_db_hist.Keys;
            ==
            t.block_slashing_db_hist.Keys;
            ==
            new_block_slashing_db_hist.Keys;
            == 
            s.block_slashing_db_hist.Keys + new_active_block_consensus_instances.Keys;
            ==
            s.block_slashing_db_hist.Keys + s.active_block_consensus_instances.Keys;
        }
    }

    lemma lem_updateBlockConsensusInstanceValidityCheckHelper(
        m: map<Slot, BlockConsensusValidityCheckState>,
        new_block_slashing_db: set<SlashingDBBlock>,
        m': map<Slot, BlockConsensusValidityCheckState>
    )    
    requires m' == updateBlockConsensusInstanceValidityCheckHelper(m, new_block_slashing_db)
    ensures m.Keys == m'.Keys
    ensures forall slot |
                && slot in m'.Keys 
                ::
                && var bcvc := m'[slot];
                && bcvc.validityPredicate == ((bb: BeaconBlock) => consensus_is_valid_beacon_block(
                                                                        new_block_slashing_db, 
                                                                        bb, 
                                                                        bcvc.proposer_duty,
                                                                        bcvc.complete_signed_randao_reveal));
  
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
                && var bcvc := m'[slot];
                && bcvc.validityPredicate == (bb: BeaconBlock) => consensus_is_valid_beacon_block(
                                                                        new_block_slashing_db, 
                                                                        bb, 
                                                                        bcvc.proposer_duty,
                                                                        bcvc.complete_signed_randao_reveal);

    }  

    lemma lem_inv_exists_db_in_block_slashing_db_hist_and_duty_for_every_validity_predicate_updateBlockSlashingDBHist(
        hist: map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>>,
        new_active_block_consensus_instances : map<Slot, BlockConsensusValidityCheckState>,
        new_block_slashing_db: set<SlashingDBBlock>,
        new_hist: map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>>
    )    
    requires new_hist == updateBlockSlashingDBHist(hist, 
                                                 new_active_block_consensus_instances, 
                                                 new_block_slashing_db)
    ensures ( forall k: Slot | k in new_hist.Keys ::
                && ( (k in new_active_block_consensus_instances.Keys)
                        ==> ( && var vp := new_active_block_consensus_instances[k].validityPredicate;
                              && var hist_k := getOrDefault(hist, k, map[]);
                              && var hist_k_vp := getOrDefault(hist_k, vp, {}) + {new_block_slashing_db};
                              && new_hist[k][vp] == hist_k_vp                        
                            )
                   )
                && ( (k !in new_active_block_consensus_instances.Keys)
                        ==> new_hist[k] == hist[k]
                   )
            )
    { }

    // lemma lem_inv_exists_db_in_block_slashing_db_hist_and_duty_for_every_validity_predicate_updateBlockConsensusInstanceValidityCheck(
    //     s: BlockConsensusEngineState,
    //     new_block_slashing_db: set<SlashingDBBlock>,
    //     r: BlockConsensusEngineState
    // )
    // requires r == updateBlockConsensusInstanceValidityCheck(s, new_block_slashing_db)        
    // requires inv_exists_db_in_block_slashing_db_hist_and_duty_for_every_validity_predicate_body_ces(s)
    // requires ( forall k: Slot | k in s.active_block_consensus_instances.Keys ::
    //                 s.active_block_consensus_instances[k].proposer_duty.slot == k )
    // ensures inv_exists_db_in_block_slashing_db_hist_and_duty_for_every_validity_predicate_body_ces(r)
    // {
    //     lem_updateBlockConsensusInstanceValidityCheck(s, new_block_slashing_db, r);
    //     assert r.block_slashing_db_hist.Keys
    //             == s.block_slashing_db_hist.Keys + s.active_block_consensus_instances.Keys;

    //     var new_active_block_consensus_instances := updateBlockConsensusInstanceValidityCheckHelper(
    //                 s.active_block_consensus_instances,
    //                 new_block_slashing_db
    //             );

    //     assert forall k: Slot | k in new_active_block_consensus_instances.Keys ::
    //                 && var ci := new_active_block_consensus_instances[k];
    //                 && ci.validityPredicate
    //                     == ((bb: BeaconBlock) => consensus_is_valid_beacon_block(
    //                                                     new_block_slashing_db, 
    //                                                     ad, 
    //                                                     ci.proposer_duty)
    //                        );
                 
        



    //     var new_block_slashing_db_hist := updateBlockSlashingDBHist(
    //                                         s.block_slashing_db_hist,
    //                                         new_active_block_consensus_instances,
    //                                         new_block_slashing_db
    //                                     );
    //     assert forall k: Slot | k in new_active_block_consensus_instances.Keys ::
    //                 && var ci := new_active_block_consensus_instances[k];
    //                 && var vp := ci.validityPredicate;
    //                 && var duty := ci.proposer_duty;
    //                 && duty.slot == k
    //                 && new_block_slashing_db in new_block_slashing_db_hist[k][vp]
    //             ;
    //     assert new_block_slashing_db_hist.Keys 
    //                 == s.block_slashing_db_hist.Keys + new_active_block_consensus_instances.Keys
    //             ;
    //     assert inv_exists_db_in_block_slashing_db_hist_and_duty_for_every_validity_predicate_body_ces(s);

    //     forall k: Slot, vp: BeaconBlock -> bool | ( && k in new_block_slashing_db_hist.Keys
    //                                                     && vp in new_block_slashing_db_hist[k]
    //                                                   )
    //     ensures ( exists db: set<SlashingDBBlock>, duty: BlockDuty ::
    //                         && duty.slot == k
    //                         && db in new_block_slashing_db_hist[k][vp]
    //                         && vp == (bb: BeaconBlock) => consensus_is_valid_beacon_block(db, ad, duty)
    //                     )
    //     {
    //         if k in new_active_block_consensus_instances.Keys
    //         {
    //             var ci := new_active_block_consensus_instances[k];                

    //             if vp == ci.validityPredicate
    //             {
    //                 var duty := ci.proposer_duty;
    //                 assert  && duty.slot == k
    //                         && new_block_slashing_db in new_block_slashing_db_hist[k][vp];
    //                 assert (exists db: set<SlashingDBBlock>, duty: BlockDuty ::
    //                         && duty.slot == k
    //                         && db in new_block_slashing_db_hist[k][vp]
    //                         && vp == (bb: BeaconBlock) => consensus_is_valid_beacon_block(db, ad, duty)
    //                     );
    //             }
    //             else 
    //             {
    //                 assert vp in s.block_slashing_db_hist[k];
    //                 assert (exists db: set<SlashingDBBlock>, duty: BlockDuty ::
    //                         && duty.slot == k
    //                         && db in s.block_slashing_db_hist[k][vp]
    //                         && vp == (bb: BeaconBlock) => consensus_is_valid_beacon_block(db, ad, duty)
    //                     );
    //             }
    //         }
    //         else
    //         {                
    //             assert k in s.block_slashing_db_hist.Keys;
    //             assert vp in s.block_slashing_db_hist[k];
    //             assert (exists db: set<SlashingDBBlock>, duty: BlockDuty ::
    //                         && duty.slot == k
    //                         && db in s.block_slashing_db_hist[k][vp]
    //                         && vp == (bb: BeaconBlock) => consensus_is_valid_beacon_block(db, ad, duty)
    //                     );                
    //         }
    //     }
     
    //     lem_updateBlockConsensusInstanceValidityCheckHelper(
    //             s.active_block_consensus_instances,
    //             new_block_slashing_db,
    //             new_active_block_consensus_instances);
    //     assert new_active_block_consensus_instances.Keys == s.active_block_consensus_instances.Keys;

    //     var t := s.(active_block_consensus_instances := new_active_block_consensus_instances,
    //                 block_slashing_db_hist := new_block_slashing_db_hist
    //                );
    //     assert inv_exists_db_in_block_slashing_db_hist_and_duty_for_every_validity_predicate_body_ces(t);
    //     assert r.block_slashing_db_hist.Keys == t.block_slashing_db_hist.Keys;
    //     assert inv_exists_db_in_block_slashing_db_hist_and_duty_for_every_validity_predicate_body_ces(r);
    // }

    // lemma lem_inv_every_db_in_block_slashing_db_hist_is_subset_of_att_slashing_db_body_updateBlockConsensusInstanceValidityCheck(
    //     s: BlockConsensusEngineState,
    //     new_block_slashing_db: set<SlashingDBBlock>,
    //     r: BlockConsensusEngineState
    // )
    // requires r == updateBlockConsensusInstanceValidityCheck(s, new_block_slashing_db)        
    // requires inv_every_db_in_block_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(s, new_block_slashing_db)
    // requires ( forall k: Slot | k in s.active_block_consensus_instances.Keys ::
    //                 s.active_block_consensus_instances[k].proposer_duty.slot == k )
    // ensures inv_every_db_in_block_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(r, new_block_slashing_db)
    // {
    //     lem_updateBlockConsensusInstanceValidityCheck(s, new_block_slashing_db, r);
    //     assert r.block_slashing_db_hist.Keys
    //             == s.block_slashing_db_hist.Keys + s.active_block_consensus_instances.Keys;

    //     var new_active_block_consensus_instances := updateBlockConsensusInstanceValidityCheckHelper(
    //                 s.active_block_consensus_instances,
    //                 new_block_slashing_db
    //             );

    //     assert forall k: Slot | k in new_active_block_consensus_instances.Keys ::
    //                 && var ci := new_active_block_consensus_instances[k];
    //                 && ci.validityPredicate
    //                     == ((bb: BeaconBlock) => consensus_is_valid_beacon_block(
    //                                                     new_block_slashing_db, 
    //                                                     ad, 
    //                                                     ci.proposer_duty)
    //                        );
                 
    //     var new_block_slashing_db_hist := updateBlockSlashingDBHist(
    //                                         s.block_slashing_db_hist,
    //                                         new_active_block_consensus_instances,
    //                                         new_block_slashing_db
    //                                     );
    //     assert forall k: Slot | k in new_active_block_consensus_instances.Keys ::
    //                 && var ci := new_active_block_consensus_instances[k];
    //                 && var vp := ci.validityPredicate;
    //                 && var duty := ci.proposer_duty;
    //                 && duty.slot == k
    //                 && new_block_slashing_db in new_block_slashing_db_hist[k][vp]
    //             ;
    //     assert forall k: Slot, vp, db | 
    //                 && k in new_active_block_consensus_instances.Keys 
    //                 && vp in new_block_slashing_db_hist[k]
    //                 && db in new_block_slashing_db_hist[k][vp]
    //                 ::
    //                 && db <= new_block_slashing_db 
    //             ;
    //     assert new_block_slashing_db_hist.Keys 
    //                 == s.block_slashing_db_hist.Keys + new_active_block_consensus_instances.Keys
    //             ;
    //     assert inv_every_db_in_block_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(s, new_block_slashing_db);

    //     forall k: Slot, vp: BeaconBlock -> bool, db | 
    //                 ( && k in new_block_slashing_db_hist.Keys
    //                   && vp in new_block_slashing_db_hist[k]
    //                   && db in new_block_slashing_db_hist[k][vp]
    //                 )
    //     ensures db <= new_block_slashing_db
    //     {
    //         if k in new_active_block_consensus_instances.Keys
    //         {
    //             var ci := new_active_block_consensus_instances[k];                

    //             if vp == ci.validityPredicate
    //             {
    //                 assert db <= new_block_slashing_db;                    
    //             }
    //             else 
    //             {
    //                 assert vp in s.block_slashing_db_hist[k];
    //                 assert db <= new_block_slashing_db;                        
    //             }
    //         }
    //         else
    //         {                
    //             assert k in s.block_slashing_db_hist.Keys;
    //             assert vp in s.block_slashing_db_hist[k];
    //             assert db <= new_block_slashing_db;                
    //         }
    //     }
     
    //     var t := s.(active_block_consensus_instances := new_active_block_consensus_instances,
    //                 block_slashing_db_hist := new_block_slashing_db_hist
    //                );
    //     assert inv_every_db_in_block_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(t, new_block_slashing_db);
    //     assert r.block_slashing_db_hist.Keys == t.block_slashing_db_hist.Keys;
    //     assert inv_every_db_in_block_slashing_db_hist_is_subset_of_att_slashing_db_body_ces(r, new_block_slashing_db);
    // }    
}