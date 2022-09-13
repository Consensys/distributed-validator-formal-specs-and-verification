include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"
include "../att_spec_proofs/fnc_inv.dfy"
include "../att_spec_proofs/helper_sets_lemmas.dfy"

module DVN_Init_Inv
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Att_Assumptions

    
    lemma dvn_init_inv1(dvn: DVState)       
    requires DV.Init(dvn, {})    
    ensures inv1(dvn)
    {}  

    lemma prop1_a(dvn: DVState, hn: BLSPubkey)       
    requires inv1(dvn)    
    requires hn in dvn.honest_nodes_states.Keys
    ensures hn in dvn.all_nodes
    ensures hn !in dvn.adversary.nodes
    {
        calc {
            hn in dvn.adversary.nodes;
            ==> 
            hn in dvn.adversary.nodes && hn in dvn.honest_nodes_states.Keys;
            ==>
            hn in dvn.honest_nodes_states.Keys * dvn.adversary.nodes;
            ==> 
            false;
        }        
    }

    lemma dvn_init_inv2(dvn: DVState)       
    requires DV.Init(dvn, {})    
    ensures inv2(dvn)
    {}    

    lemma dvn_init_inv3(dvn: DVState)       
    requires DV.Init(dvn, {})    
    ensures inv3(dvn)
    {}    

    lemma dvn_init_inv4(dvn: DVState)
    requires DV.Init(dvn, {})    
    ensures inv4(dvn)
    {}

}