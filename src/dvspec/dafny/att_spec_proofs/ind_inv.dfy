include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"

module Att_Ind_Inv_With_Empty_Initial_Attestation_Slashing_DB
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV    
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB

    lemma ConsensusSpec_Init_implies_inv41<D(!new, 0)>(dvn: DVState, ci: ConsensusInstance<D>)
    requires ConsensusSpec.Init(ci, dvn.all_nodes, dvn.honest_nodes_states.Keys)
    ensures inv41(ci)
    { } 

    lemma NextConsensusDecides_implies_inv41<D(!new, 0)>(
            s: ConsensusInstance,
            honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,        
            s': ConsensusInstance
        )
    requires inv41(s) && isConditionForSafetyTrue(s)
    requires ConsensusSpec.NextConsensusDecides(s, honest_nodes_validity_predicates, s')
    ensures inv41(s')
    { } 

    lemma ConsensusSpec_Next_implies_inv41<D(!new, 0)>(
            s: ConsensusInstance,
            honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,        
            s': ConsensusInstance,
            output: Optional<OutCommand>
        )
    requires inv41(s) && isConditionForSafetyTrue(s)
    requires ConsensusSpec.Next(s, honest_nodes_validity_predicates, s', output)
    ensures inv41(s')
    { 
        assert NextConsensusDecides(s, honest_nodes_validity_predicates, s');
        NextConsensusDecides_implies_inv41(s, honest_nodes_validity_predicates, s');
        assert inv41(s');
        assert NextNodeStep(s', honest_nodes_validity_predicates, output);
        assert inv41(s');
    }

    lemma DV_Init_implies_inv41(dvn: DVState)
    requires DV.Init(dvn, {}) 
    ensures forall s: Slot :: inv41(dvn.consensus_on_attestation_data[s])
    { } 

    // TODO: Remove {:axiom} and prove this lemma later.
    lemma {:axiom} DV_Next_implies_inv41(dvn: DVState, dvn': DVState)
    requires forall s: Slot :: inv41(dvn.consensus_on_attestation_data[s])
    requires exists event: DV.Event :: DV.NextEvent(dvn, event, dvn')
    ensures forall s: Slot :: inv41(dvn'.consensus_on_attestation_data[s])
   
    lemma a_valid_decided_value_has_at_least_f_plus_1_honest_nodes(s: ConsensusInstance<AttestationData>)
    requires is_a_valid_decided_value(s)
    ensures exists h_nodes |
                && h_nodes <= s.honest_nodes_validity_functions.Keys  
                && |h_nodes| >= quorum(|s.all_nodes|) - (|s.all_nodes| - |s.honest_nodes_status.Keys|)
                ::
                honest_nodes_with_validityPredicate(s, h_nodes)
    {}


    lemma DV_Init_implies_inv42(dvn: DVState)
    requires DV.Init(dvn, {}) 
    ensures inv42(dvn)
    { } 

    // TODO: Remove {:axiom} and prove this lemma later.
    lemma {:axiom} DV_Next_implies_inv42(dvn: DVState, dvn': DVState)
    requires inv42(dvn)
    requires exists event: DV.Event :: DV.NextEvent(dvn, event, dvn')
    ensures inv42(dvn')

    
    lemma DV_Init_implies_thresholds(dvn: DVState)
    requires DV.Init(dvn, {})
    ensures |dvn.honest_nodes_states.Keys| >= |dvn.all_nodes| - f(|dvn.all_nodes|) 
}