include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"
include "../att_spec_proofs/core_proofs.dfy"
include "../att_spec_proofs/ci_ind_inv.dfy"
include "../att_spec_proofs/dvc_ind_inv.dfy"
include "../att_spec_proofs/dvn_ind_inv.dfy"

module Proof_Test
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Att_Ind_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Helper_Sets_Lemmas

    lemma inv53(dvn: DVState, s: Slot)
    ensures && var ci := dvn.consensus_on_attestation_data[s];
            // && quorum(|ci.all_nodes|) <= |ci.honest_nodes_status|
            && dvn.all_nodes == ci.all_nodes
            && dvn.honest_nodes_states.Keys == ci.honest_nodes_status.Keys
    {}
}