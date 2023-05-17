include "../../../common/commons.dfy"

include "dvc_block_proposer_instrumented.dfy"
include "../../../specs/consensus/consensus.dfy"
include "../../../specs/network/network.dfy"
include "../supporting_lemmas/inv.dfy"
include "../../bn_axioms.dfy"
include "../../rs_axioms.dfy"


module Common_Proofs_For_Block_Proposer
{
    import opened Types 
    import opened Common_Functions
    import opened Set_Seq_Helper
    import opened Signing_Methods
    import opened Consensus
    import opened Network_Spec
    import opened Block_DVC
    import opened Consensus_Engine
    import opened Block_DV
    import opened Block_Inv_With_Empty_Initial_Block_Slashing_DB
    import opened BN_Axioms
    import opened RS_Axioms

    lemma lem_f_update_block_consensus_engine_state(
        s: ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>,
        new_block_slashing_db: set<SlashingDBBlock>,        
        r: ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>
    )
    requires r == f_update_block_consensus_engine_state(s, new_block_slashing_db)        
    ensures r.slashing_db_hist.Keys
                == s.slashing_db_hist.Keys + s.active_consensus_instances.Keys
    {
        var new_active_consensus_instances := f_update_block_consensus_instance_validity_check_states(
                    s.active_consensus_instances,
                    new_block_slashing_db
                );

        lem_f_update_block_consensus_instance_validity_check_states(
                s.active_consensus_instances,
                new_block_slashing_db,
                new_active_consensus_instances);

        assert new_active_consensus_instances.Keys == s.active_consensus_instances.Keys;

        var new_slashing_db_hist := f_update_block_slashing_db_hist_with_new_consensus_instances_and_slashing_db_blocks(
                                            s.slashing_db_hist,
                                            new_active_consensus_instances,
                                            new_block_slashing_db
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

    lemma lem_f_update_block_consensus_instance_validity_check_states(
        m: map<Slot, BlockConsensusValidityCheckState>,
        new_block_slashing_db: set<SlashingDBBlock>,
        m': map<Slot, BlockConsensusValidityCheckState>
    )    
    requires m' == f_update_block_consensus_instance_validity_check_states(m, new_block_slashing_db)
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
            lem_map_keys_has_one_entry_in_items(m, k);
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