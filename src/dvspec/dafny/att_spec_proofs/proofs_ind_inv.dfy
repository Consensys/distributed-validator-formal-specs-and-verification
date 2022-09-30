include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"
include "../att_spec_proofs/fnc_invs_1_26.dfy"
include "../att_spec_proofs/helper_sets_lemmas.dfy"
include "../att_spec_proofs/proofs_intermediate_steps.dfy"
include "../att_spec_proofs/dvn_next_invs_1_7.dfy"
include "../att_spec_proofs/dvn_next_invs_8_18.dfy"
include "../att_spec_proofs/dvn_next_invs_19_26.dfy"
include "../att_spec_proofs/dvn_next_invs_27_37.dfy"
include "ind_inv.dfy"
include "ind_inv2.dfy"
include "ind_inv3.dfy"
include "core_proofs.dfy"


module Proofs_DVN_Ind_Inv
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Att_Ind_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Att_Assumptions
    import opened Fnc_Invs_1_26
    import opened Helper_Sets_Lemmas
    import opened DVN_Next_Invs_1_7
    import opened DVN_Next_Invs_8_18
    import opened DVN_Next_Invs_19_26
    import opened Proofs_Intermediate_Steps
    import opened DVN_Next_Invs_27_37
    import opened Core_Proofs
    import opened IndInv3

    predicate ind_inv(dvn: DVState)       
    {
        && invs_1_7(dvn)
        && invs_8_18(dvn)
        && invs_19_26(dvn)
        && invs_27_37(dvn)
        && invs_other_properties(dvn)
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
    
    predicate invs_19_26(dvn: DVState)       
    {        
        &&  inv19(dvn)           
        &&  inv21(dvn) 
        &&  inv22(dvn)      
        &&  inv23(dvn)  
        &&  inv25(dvn)          
        &&  inv26(dvn)  
    }

    predicate invs_27_37(dvn: DVState)       
    {                
        &&  inv27(dvn)  
        &&  inv28(dvn)  
        &&  inv29(dvn)  
        &&  inv31(dvn)  
        &&  inv34(dvn)
        &&  inv35(dvn)
        &&  inv36(dvn)
        &&  inv37(dvn)
    }

    predicate invs_other_properties(dvn: DVState)       
    {                
        // &&  inv46_b(dvn)
        && pred_4_1_b(dvn)     
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
        lemma_ind_inv_dvn_next_invs_19_26(dvn, dvn');
        lemma_ind_inv_dvn_next_invs_27_37(dvn, dvn');
        lemma_ind_inv_dvn_other_properties(dvn, dvn');       
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
        // TODO: Error: ... System.Threading.Thread.StartCallback() ...
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

    lemma lemma_ind_inv_dvn_next_invs_19_26(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    requires ind_inv(dvn)
    ensures invs_19_26(dvn')        
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

    lemma lemma_ind_inv_dvn_next_invs_27_37(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    requires ind_inv(dvn)
    ensures invs_27_37(dvn') 
    {
        var e: DV.Event :| DV.NextEvent(dvn, e, dvn');
        lemma_inv27_dvn_next(dvn, e, dvn');    
        lemma_inv28_dvn_next(dvn, e, dvn');  
        lemma_inv29_dvn_next(dvn, e, dvn');          
        lemma_inv31_dvn_next(dvn, e, dvn');  
        lemma_inv34_dvn_next(dvn, e, dvn');  
        lemma_inv35_dvn_next(dvn, e, dvn');  
        lemma_inv36_dvn_next(dvn, e, dvn');  
        lemma_inv37_dvn_next(dvn, e, dvn');  
    }

    lemma lemma_ind_inv_dvn_other_properties(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    requires ind_inv(dvn)
    ensures invs_other_properties(dvn')
    {
        var e: DV.Event :| DV.NextEvent(dvn, e, dvn');        
        lemma_ind_inv_dvn_next_inv_pred_4_1_b(dvn, e, dvn');                  
    }

    // TODO
    // lemma lemma_ind_inv_dvn_next_properties(dvn: DVState, dvn': DVState)       
    // requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    // requires ind_inv(dvn)
    // ensures prop_monotonic_set_of_in_transit_messages(dvn, dvn')
    // {
    //     var e: DV.Event :| DV.NextEvent(dvn, e, dvn');        
    //     lemma_prop_monotonic_set_of_in_transit_messages_ind_inv(dvn, dvn');                  
    // }

    lemma lemma_prop_monotonic_set_of_in_transit_messages_ind_inv(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')    
    ensures prop_monotonic_set_of_in_transit_messages(dvn, dvn')
    {
        var e: DV.Event :| DV.NextEvent(dvn, e, dvn');        
        assert prop_monotonic_set_of_in_transit_messages(dvn, dvn');
    }

    lemma lemma_ind_inv_implies_intermediate_steps(dvn: DVState)
    requires ind_inv(dvn)
    ensures inv11(dvn)
    ensures inv12(dvn)
    ensures inv14(dvn)
    ensures inv15(dvn)
    ensures inv24(dvn)    
    ensures inv50(dvn)
    ensures inv51(dvn)   
    ensures inv53(dvn)    
    ensures construct_signed_attestation_signature_assumptions_helper(
                dvn.construct_signed_attestation_signature,
                dvn.dv_pubkey,
                dvn.all_nodes)  
    {    
        lemma_inv11_ind_inv(dvn);
        lemma_inv12_ind_inv(dvn);
        lemma_inv14_ind_inv(dvn);
        lemma_inv15_ind_inv(dvn);
        lemma_inv24_ind_inv(dvn);
        lemma_inv50_ind_inv(dvn);
        lemma_inv51_ind_inv(dvn);
        lemma_inv53_ind_inv(dvn);      
        lemma_construct_signed_attestation_signature_assumptions_helper(dvn);       
    }

    // TODO
    // lemma lemma_ind_inv_dvn_next_inv_46_b(dvn: DVState, dvn': DVState)       
    // requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    // requires ind_inv(dvn)
    // // ensures 46_b(dvn')
    // {
        

    //     lemma_inv29_inv_attestation_consensus_active_instances_predicate_is_in_att_slashing_db_hist(dvn);
    //     assert inv_attestation_consensus_active_instances_predicate_is_in_att_slashing_db_hist(dvn);

    //     lemma_inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(dvn);
    //     assert inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(dvn);

    //     lemma_ind_inv_implies_intermediate_steps(dvn);
    //     assert inv53(dvn);

    //     var e: DV.Event :| DV.NextEvent(dvn, e, dvn');  

    //     assert && inv46_b(dvn)
    //            && inv1(dvn)
    //            && inv53(dvn)
    //            && inv3(dvn)    
    //            && inv33(dvn)  
    //            && inv46_b(dvn);
    //     // lemma_inv46_b(dvn, e, dvn');    

    //     //assert inv46_b(dvn');
    // }

    lemma lemma_ind_inv_dvn_next_inv_pred_4_1_b(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEvent(dvn, e, dvn')
    requires ind_inv(dvn)
    ensures pred_4_1_b(dvn')
    {
        lemma_ind_inv_implies_intermediate_steps(dvn);
        assert construct_signed_attestation_signature_assumptions_helper(
                dvn.construct_signed_attestation_signature,
                dvn.dv_pubkey,
                dvn.all_nodes);

        lemma_inv36_invNetwork(dvn);
        assert invNetwork(dvn);

        lemma_inv37_pred_rcvd_attestation_shares_is_in_all_messages_sent(dvn);
        assert pred_rcvd_attestation_shares_is_in_all_messages_sent(dvn);

        lemma_pred_4_1_b(dvn, e, dvn');
        assert pred_4_1_b(dvn');
    }
}