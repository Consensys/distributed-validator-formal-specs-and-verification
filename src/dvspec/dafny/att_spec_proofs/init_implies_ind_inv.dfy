include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"

module Init_IndInv
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened AttInvariants
    
    lemma init_implies_inv1(dvn: DVState)       
    requires exists initial_attestation_slashing_db: set<SlashingDBAttestation> :: 
                DV.Init(dvn, initial_attestation_slashing_db)        
    ensures forall i: Slot :: no_conflict_decisions_pred1_in_sec_3_1(dvn.consensus_on_attestation_data[i])
    {}

    lemma honest_node_inconsensus_init_satisfies_inv2<D(!new, 0)>(
        s: ConsensusInstance, 
        all_nodes: set<BLSPubkey>, 
        honest_nodes: set<BLSPubkey>,
        n: BLSPubkey)
    requires ConsensusSpec.Init(s, all_nodes, honest_nodes)
    requires ConsensusSpec.isConditionForSafetyTrue(s)
    requires n in s.honest_nodes_status.Keys
    ensures s.honest_nodes_status[n] == NOT_DECIDED
    { 
        assert forall t | t in s.honest_nodes_status.Values :: t == NOT_DECIDED;
        assert s.honest_nodes_status[n] in s.honest_nodes_status.Values;
        assert s.honest_nodes_status[n] == NOT_DECIDED;
    }       


    lemma consensus_init_implies_inv2<D(!new, 0)>(
        s: ConsensusInstance, 
        all_nodes: set<BLSPubkey>, 
        honest_nodes: set<BLSPubkey>)
    requires ConsensusSpec.Init(s, all_nodes, honest_nodes)
    requires ConsensusSpec.isConditionForSafetyTrue(s)    
    ensures no_decisions_pred2_in_sec_3_1(s)
    { 
        var unchecked_honest_nodes := honest_nodes;
        var checked_honest_nodes := {};

        while unchecked_honest_nodes != {}
            invariant honest_nodes == unchecked_honest_nodes + checked_honest_nodes
            invariant unchecked_honest_nodes * checked_honest_nodes == {}
            invariant checked_honest_nodes <= honest_nodes
            invariant unchecked_honest_nodes <= honest_nodes
            invariant forall i: BLSPubkey | i in checked_honest_nodes :: s.honest_nodes_status[i] == NOT_DECIDED
            decreases |unchecked_honest_nodes|
        {
            var i :| i in unchecked_honest_nodes;
            honest_node_inconsensus_init_satisfies_inv2(s, all_nodes, honest_nodes, i);
            unchecked_honest_nodes := unchecked_honest_nodes - {i};
            checked_honest_nodes := checked_honest_nodes + {i};
        }
    }       
}



