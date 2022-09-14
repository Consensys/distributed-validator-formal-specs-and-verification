include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"
include "../att_spec_proofs/fnc_inv.dfy"
include "../att_spec_proofs/helper_sets_lemmas.dfy"
include "../att_spec_proofs/dvn_next_inv.dfy"

module Proofs_DVN_Ind_Inv
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Att_Assumptions
    import opened Fnc_Inv
    import opened Helper_Sets_Lemmas
    import opened DVN_Next_Inv

    predicate ind_inv(dvn: DVState)       
    {
        &&  inv1(dvn)
        &&  inv2(dvn)
        &&  inv3(dvn)
        &&  inv4(dvn)
        &&  inv5(dvn)
        &&  inv6(dvn)
        &&  inv7(dvn)    
        &&  inv8(dvn)   
        &&  inv9(dvn)  
        &&  inv10(dvn) 
        &&  inv11(dvn)  
        &&  inv12(dvn)  
        &&  inv14(dvn)  
        &&  inv15(dvn)  
    }

    lemma lemma_ind_inv_dvn_init(dvn: DVState)       
    requires DV.Init(dvn, {})    
    ensures ind_inv(dvn)
    {}  

    lemma lemma_ind_inv_dvn_next_invs_1_7(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    requires ind_inv(dvn)
    // ensures ind_inv(dvn')
    {
        var e: DV.Event :| DV.NextEvent(dvn, e, dvn');
        lemma_inv1_dvn_next(dvn, e, dvn');
        lemma_inv2_dvn_next(dvn, e, dvn');
        lemma_inv3_dvn_next(dvn, e, dvn');
        lemma_inv4_dvn_next(dvn, e, dvn');
        lemma_inv5_dvn_next(dvn, e, dvn');
        lemma_inv6_dvn_next(dvn, e, dvn');
        lemma_inv7_dvn_next(dvn, e, dvn');
        
        
        /*
        // Error: ... System.Threading.Thread.StartCallback() ...
        lemma_inv10_dvn_next(dvn, e, dvn');       
        lemma_inv11_dvn_next(dvn, e, dvn');
        lemma_inv12_dvn_next(dvn, e, dvn');        
        lemma_inv14_dvn_next(dvn, e, dvn');
        */
        
    }

    lemma lemma_ind_inv_dvn_next_invs_8_14(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    requires ind_inv(dvn)
    // ensures ind_inv(dvn')
    {
        var e: DV.Event :| DV.NextEvent(dvn, e, dvn');
        lemma_inv8_dvn_next(dvn, e, dvn');
        lemma_inv9_dvn_next(dvn, e, dvn');
        lemma_inv10_dvn_next(dvn, e, dvn');        
        lemma_inv11_dvn_next(dvn, e, dvn');
        lemma_inv12_dvn_next(dvn, e, dvn');
        lemma_inv13_dvn_next(dvn, e, dvn');
        lemma_inv14_dvn_next(dvn, e, dvn');
        lemma_inv15_dvn_next(dvn, e, dvn');
    }

    lemma lemma_ind_inv_implies_other_invs(dvn: DVState)
    requires ind_inv(dvn)
    ensures inv53(dvn)    
    {
        lemma_inv2_inv53(dvn);
    }

    lemma lemma_inv2_inv53(dvn: DVState)
    requires inv2(dvn)
    ensures inv53(dvn)
    { }
}