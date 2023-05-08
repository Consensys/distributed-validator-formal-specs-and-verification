include "../../../common/commons.dfy"

include "dvc_block_proposer_instrumented.dfy"
include "../../../specs/consensus/consensus.dfy"
include "../../../specs/network/network.dfy"
include "../supporting_lemmas/inv.dfy"
include "../../common/helper_sets_lemmas.dfy"
include "../../bn_axioms.dfy"
include "../../rs_axioms.dfy"


module Common_Proofs_For_Block_Proposer
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Block_Proposer_Spec_Instr
    import opened Block_Consensus_Engine_Instr
    import opened DV_Block_Proposer_Spec
    import opened Block_Inv_With_Empty_Initial_Block_Slashing_DB
    import opened Helper_Sets_Lemmas
    import opened Block_BN_Axioms
    import opened RS_Axioms

    lemma lem_updateConsensusInstanceValidityCheck(
        s: BlockConsensusEngineState,
        new_block_slashing_db: set<SlashingDBBlock>,        
        r: BlockConsensusEngineState
    )
    requires r == updateConsensusInstanceValidityCheck(s, new_block_slashing_db)        
    ensures r.block_slashing_db_hist.Keys
                == s.block_slashing_db_hist.Keys + s.active_consensus_instances_on_beacon_blocks.Keys
    {
        var new_active_consensus_instances_on_beacon_blocks := updateConsensusInstanceValidityCheckHelper(
                    s.active_consensus_instances_on_beacon_blocks,
                    new_block_slashing_db
                );

        lem_updateConsensusInstanceValidityCheckHelper(
                s.active_consensus_instances_on_beacon_blocks,
                new_block_slashing_db,
                new_active_consensus_instances_on_beacon_blocks);

        assert new_active_consensus_instances_on_beacon_blocks.Keys == s.active_consensus_instances_on_beacon_blocks.Keys;

        var new_block_slashing_db_hist := updateBlockSlashingDBHist(
                                            s.block_slashing_db_hist,
                                            new_active_consensus_instances_on_beacon_blocks,
                                            new_block_slashing_db
                                        );

        assert new_block_slashing_db_hist.Keys 
                    == s.block_slashing_db_hist.Keys + new_active_consensus_instances_on_beacon_blocks.Keys;

        var t := s.(active_consensus_instances_on_beacon_blocks := new_active_consensus_instances_on_beacon_blocks,
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
            s.block_slashing_db_hist.Keys + new_active_consensus_instances_on_beacon_blocks.Keys;
            ==
            s.block_slashing_db_hist.Keys + s.active_consensus_instances_on_beacon_blocks.Keys;
        }
    }

    lemma lem_updateConsensusInstanceValidityCheckHelper(
        m: map<Slot, BlockConsensusValidityCheckState>,
        new_block_slashing_db: set<SlashingDBBlock>,
        m': map<Slot, BlockConsensusValidityCheckState>
    )    
    requires m' == updateConsensusInstanceValidityCheckHelper(m, new_block_slashing_db)
    ensures m.Keys == m'.Keys
    ensures forall slot |
                && slot in m'.Keys 
                ::
                && var bcvc := m'[slot];
                && bcvc.validityPredicate == ((bb: BeaconBlock) => ci_decision_is_valid_beacon_block(
                                                                        new_block_slashing_db, 
                                                                        bb, 
                                                                        bcvc.proposer_duty,
                                                                        bcvc.randao_reveal));
  
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
                && bcvc.validityPredicate == (bb: BeaconBlock) => ci_decision_is_valid_beacon_block(
                                                                        new_block_slashing_db, 
                                                                        bb, 
                                                                        bcvc.proposer_duty,
                                                                        bcvc.randao_reveal);

    }  
}