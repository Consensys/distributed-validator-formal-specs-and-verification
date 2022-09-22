include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"
include "../att_spec_proofs/fnc_inv.dfy"
include "../att_spec_proofs/helper_sets_lemmas.dfy"
include "../att_spec_proofs/proofs_intermediate_steps.dfy"
include "../att_spec_proofs/dvn_next_invs_1_7.dfy"
include "../att_spec_proofs/dvn_next_invs_8_18.dfy"
include "../att_spec_proofs/dvn_next_invs_19.dfy"


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
    import opened DVN_Next_Invs_1_7
    import opened DVN_Next_Invs_8_18
    import opened DVN_Next_Invs_19
    import opened Proofs_Intermediate_Steps

    predicate ind_inv(dvn: DVState)       
    {
        && invs_1_7(dvn)
        && invs_8_18(dvn)
        && invs_19(dvn)
    }

    predicate invs_1_7(dvn: DVState)       
    {
        &&  inv1(dvn)
        &&  inv2(dvn)
        &&  inv3(dvn)
        &&  inv4(dvn)
        &&  inv5(dvn)
        &&  inv6(dvn)
        &&  inv7(dvn)            
    }

    predicate invs_8_18(dvn: DVState)       
    {        
        &&  inv8(dvn)   
        &&  inv9(dvn)  
        &&  inv10(dvn) 
        &&  inv13(dvn)      
        &&  inv16(dvn)  
        &&  inv17(dvn)  
        &&  inv18(dvn)  
    }

    predicate invs_19(dvn: DVState)       
    {        
        &&  inv19(dvn)           
        &&  inv21(dvn) 
        &&  inv22(dvn)      
        &&  inv23(dvn)  
        &&  inv25(dvn)          
        &&  inv26(dvn)  
    }

    lemma lemma_ind_inv_dvn_init(dvn: DVState)       
    requires DV.Init(dvn, {})    
    ensures ind_inv(dvn)
    {}  

    lemma lemma_ind_inv_dvn_next_ind_inv(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    requires ind_inv(dvn)
    ensures ind_inv(dvn')
    {
        lemma_ind_inv_dvn_next_invs_1_7(dvn, dvn');
        lemma_ind_inv_dvn_next_invs_8_18(dvn, dvn');
        lemma_ind_inv_dvn_next_invs_19(dvn, dvn');
    }

    lemma lemma_ind_inv_dvn_next_invs_1_7(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    requires ind_inv(dvn)
    ensures invs_1_7(dvn')
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
        */
    }

    lemma lemma_ind_inv_dvn_next_invs_8_18(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    requires ind_inv(dvn)
    ensures invs_8_18(dvn')
    {
        var e: DV.Event :| DV.NextEvent(dvn, e, dvn');
        lemma_inv8_dvn_next(dvn, e, dvn');
        lemma_inv9_dvn_next(dvn, e, dvn');
        lemma_inv10_dvn_next(dvn, e, dvn');        
        lemma_inv13_dvn_next(dvn, e, dvn');                
        lemma_inv16_dvn_next(dvn, e, dvn');
        lemma_inv17_dvn_next(dvn, e, dvn');
        lemma_inv18_dvn_next(dvn, e, dvn');
    }

    lemma lemma_ind_inv_dvn_next_invs_19(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    requires ind_inv(dvn)
    ensures invs_19(dvn')        
    {
        var e: DV.Event :| DV.NextEvent(dvn, e, dvn');
        lemma_inv19_dvn_next(dvn, e, dvn');
        lemma_inv20_dvn_next(dvn, e, dvn');
        lemma_inv21_dvn_next(dvn, e, dvn');        
        lemma_inv22_dvn_next(dvn, e, dvn');                
        lemma_inv23_dvn_next(dvn, e, dvn');                
        lemma_inv25_dvn_next(dvn, e, dvn');    
        lemma_inv26_dvn_next(dvn, e, dvn');    
    }

    lemma lemma_ind_inv_implies_other_invs(dvn: DVState)
    requires ind_inv(dvn)
    ensures inv11(dvn)
    ensures inv12(dvn)
    ensures inv14(dvn)
    ensures inv15(dvn)
    ensures inv24(dvn)
    ensures inv53(dvn)    
    ensures inv51(dvn)    
    {    
        lemma_inv53_ind_inv(dvn);
        lemma_inv15_ind_inv(dvn);
        lemma_inv14_ind_inv(dvn);
        lemma_inv12_ind_inv(dvn);
        lemma_inv11_ind_inv(dvn);
        lemma_inv24_ind_inv(dvn);
        lemma_inv51_ind_inv(dvn);
    }
}