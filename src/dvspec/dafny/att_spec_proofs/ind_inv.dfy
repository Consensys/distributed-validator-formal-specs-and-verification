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


    
}