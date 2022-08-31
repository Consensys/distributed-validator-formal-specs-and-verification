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
    ensures forall i: Slot :: inv1_in_sec_3_1_no_conflict_decisions(dvn.consensus_on_attestation_data[i])
    {}

    lemma honest_node_in_consensus_init_satisfies_inv2<D(!new, 0)>(
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
    ensures inv2_in_sec_3_1_no_decisions(s)
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
            honest_node_in_consensus_init_satisfies_inv2(s, all_nodes, honest_nodes, i);
            unchecked_honest_nodes := unchecked_honest_nodes - {i};
            checked_honest_nodes := checked_honest_nodes + {i};
        }
    }   


    lemma init_implies_inv2(dvn: DVState)       
    requires exists initial_attestation_slashing_db: set<SlashingDBAttestation> :: 
                DV.Init(dvn, initial_attestation_slashing_db)        
    ensures forall i: Slot :: inv2_in_sec_3_1_no_decisions(dvn.consensus_on_attestation_data[i])
    {
        forall i: Slot
        ensures inv2_in_sec_3_1_no_decisions(dvn.consensus_on_attestation_data[i]);
        {
            assert ConsensusSpec.Init(dvn.consensus_on_attestation_data[i], dvn.all_nodes, dvn.honest_nodes_states.Keys);
            assert ConsensusSpec.isConditionForSafetyTrue(dvn.consensus_on_attestation_data[i]);
            consensus_init_implies_inv2(dvn.consensus_on_attestation_data[i], dvn.all_nodes, dvn.honest_nodes_states.Keys);        
            assert inv2_in_sec_3_1_no_decisions(dvn.consensus_on_attestation_data[i]);
        }                    
    }    


    lemma init_implies_inv3(dvn: DVState)       
    requires exists initial_attestation_slashing_db: set<SlashingDBAttestation> :: 
                DV.Init(dvn, initial_attestation_slashing_db)        
    ensures inv3_in_sec_3_2_consistant_att_slashing_databases_between_honest_nodes(dvn)
    {}    

    lemma init_implies_inv4(dvn: DVState)       
    requires exists initial_attestation_slashing_db: set<SlashingDBAttestation> :: 
                DV.Init(dvn, initial_attestation_slashing_db)        
    // ensures pred4_in_sec_3_2_consistant_slashing_db(dvn)
    {
        var pubkey: BLSPubkey :| is_honest_node(dvn, pubkey);
        var nState := dvn.honest_nodes_states[pubkey];
        var db := nState.attestation_slashing_db;        
    }  

    lemma init_implies_inv5(dvn: DVState)       
    requires exists initial_attestation_slashing_db: set<SlashingDBAttestation> :: 
                DV.Init(dvn, initial_attestation_slashing_db)        
    ensures pred5_in_sec_3_3_curr_att_duty_is_last_served_duty(dvn)
    { }  

    lemma init_implies_inv100(dvn: DVState)       
    requires exists initial_attestation_slashing_db: set<SlashingDBAttestation> :: 
                DV.Init(dvn, initial_attestation_slashing_db)        
    ensures forall pubkey: BLSPubkey | pubkey in dvn.all_nodes ::
                    || pubkey in dvn.honest_nodes_states.Keys
                    || pubkey in dvn.adversary.nodes
    { }  
}



