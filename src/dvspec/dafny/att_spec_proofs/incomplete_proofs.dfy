include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"
include "../att_spec_proofs/fnc_inv.dfy"
include "../att_spec_proofs/dvn_next_inv.dfy"
include "../att_spec_proofs/helper_sets_lemmas.dfy"


module Incomplete_Proofs 
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB    
    import opened Helper_Sets_Lemmas
    import opened DVN_Next_Inv
    import opened Fnc_Inv    

    lemma {:axiom} axiom_inv15(dvc: DVCNodeState)    
    ensures inv15_body(dvc)

    
    
    

    

    
      
    
}