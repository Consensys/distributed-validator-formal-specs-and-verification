include "../../common/commons.dfy"
include "common/dvc_spec.dfy"
include "../../specs/consensus/consensus.dfy"
include "../../specs/network/network.dfy"
include "../../specs/dvn/dvn.dfy"
include "inv.dfy"
include "fnc_invs_1_26.dfy"
include "helper_sets_lemmas.dfy"
include "proofs_intermediate_steps.dfy"
include "dvn_next_invs_1_7.dfy"
include "dvn_next_invs_8_18.dfy"
include "dvn_next_invs_19_26.dfy"
include "dvn_next_invs_27_37.dfy"
include "ind_inv.dfy"
include "ind_inv2.dfy"
include "ind_inv3.dfy"
include "ind_inv4.dfy"
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
    import opened Att_Ind_Inv_With_Empty_Initial_Attestation_Slashing_DB2
    import opened Fnc_Invs_1_26
    import opened Helper_Sets_Lemmas
    import opened DVN_Next_Invs_1_7
    import opened DVN_Next_Invs_8_18
    import opened DVN_Next_Invs_19_26
    import opened Proofs_Intermediate_Steps
    import opened DVN_Next_Invs_27_37
    import opened Core_Proofs
    import opened IndInv3
    import opened IndInv4

    predicate ind_inv(dvn: DVState)       
    {
        && invs_1_7(dvn)
        && invs_8_18(dvn)
        && invs_19_26(dvn)
        && invs_27_37(dvn)
        && invs_other_properties_1(dvn)
        && invs_other_properties_2(dvn)
        && invs_other_properties_3(dvn)
        && invs_other_properties_4(dvn)
        && invs_other_properties_5(dvn)
        && invs_other_properties_6(dvn)
        && invs_other_properties_7(dvn)
        && inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue(dvn)
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
        &&  IndInv3.inv33(dvn)
    }


    
    lemma lemma_ind_inv_dvn_init(dvn: DVState)       
    requires DV.Init(dvn, {})    
    ensures ind_inv(dvn)
    ensures NextPreCond(dvn)
    {
        assert  DV.Init(dvn, {})  
                ==>                 
                && invs_1_7(dvn)
                && invs_8_18(dvn)
                && invs_19_26(dvn)
                && invs_27_37(dvn);

        assert  DV.Init(dvn, {})    
                ==>
                && invs_other_properties_1(dvn)
                && invs_other_properties_2(dvn)
                && invs_other_properties_3(dvn)
                && invs_other_properties_4(dvn)
                && invs_other_properties_5(dvn)
                && invs_other_properties_6(dvn)
                ;
    }  

    

    

    lemma lemma_ind_inv_dvn_next_invs_1_7(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures invs_1_7(dvn')
    {    
        lemma_inv1_dvn_next(dvn, e, dvn');
        lemma_inv2_dvn_next(dvn, e, dvn');
        lemma_inv3_dvn_next(dvn, e, dvn');
        lemma_inv4_dvn_next(dvn, e, dvn');
        lemma_inv5_dvn_next(dvn, e, dvn');
        lemma_inv6_dvn_next(dvn, e, dvn');
        lemma_inv7_dvn_next(dvn, e, dvn');        
    }

    lemma lemma_ind_inv_dvn_next_invs_8_18_helper_1(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures inv8(dvn')
    ensures inv9(dvn')
    ensures inv10(dvn')
    ensures inv13(dvn')
    {
        lemma_inv8_dvn_next(dvn, e, dvn');
        lemma_inv9_dvn_next(dvn, e, dvn');
        lemma_inv10_dvn_next(dvn, e, dvn');        
        lemma_inv13_dvn_next(dvn, e, dvn');                
        // lemma_inv16_dvn_next(dvn, e, dvn');
        // lemma_inv17_dvn_next(dvn, e, dvn');
        // lemma_inv18_dvn_next(dvn, e, dvn');
    }

    lemma lemma_ind_inv_dvn_next_invs_8_18_helper_2(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures inv16(dvn')
    ensures inv17(dvn')
    ensures inv18(dvn')
    {
        lemma_inv16_dvn_next(dvn, e, dvn');
        lemma_inv17_dvn_next(dvn, e, dvn');
        lemma_inv18_dvn_next(dvn, e, dvn');
    }

    lemma lemma_ind_inv_dvn_next_invs_8_18(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures invs_8_18(dvn')
    {
        lemma_ind_inv_dvn_next_invs_8_18_helper_1(dvn, e, dvn');
        lemma_ind_inv_dvn_next_invs_8_18_helper_2(dvn, e, dvn');
    }

    lemma lemma_ind_inv_dvn_next_invs_19_26_helper_1(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures inv19(dvn')        
    ensures inv20(dvn, dvn')
    ensures inv21(dvn')
    ensures inv22(dvn')
    {
        lemma_inv19_dvn_next(dvn, e, dvn');
        lemma_inv20_dvn_next(dvn, e, dvn');
        lemma_inv21_dvn_next(dvn, e, dvn');        
        lemma_inv22_dvn_next(dvn, e, dvn');                
        // lemma_inv23_dvn_next(dvn, e, dvn');                
        // lemma_inv25_dvn_next(dvn, e, dvn');    
        // lemma_inv26_dvn_next(dvn, e, dvn');    
    }

    lemma lemma_ind_inv_dvn_next_invs_19_26_helper_2(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures inv23(dvn')        
    ensures inv25(dvn')
    ensures inv26(dvn')
    {
        lemma_inv23_dvn_next(dvn, e, dvn');                
        lemma_inv25_dvn_next(dvn, e, dvn');    
        lemma_inv26_dvn_next(dvn, e, dvn');    
    }

    lemma lemma_ind_inv_dvn_next_invs_19_26(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures invs_19_26(dvn')        
    {
        lemma_ind_inv_dvn_next_invs_19_26_helper_1(dvn, e, dvn');
        lemma_ind_inv_dvn_next_invs_19_26_helper_2(dvn, e, dvn');
    }

    lemma lemma_ind_inv_dvn_next_invs_27_37_helper1(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures inv27(dvn') 
    ensures inv28(dvn')
    ensures inv29(dvn')
    {
        lemma_inv27_dvn_next(dvn, e, dvn');    
        lemma_inv28_dvn_next(dvn, e, dvn');  
        lemma_inv29_dvn_next(dvn, e, dvn');          
    }

    lemma lemma_ind_inv_dvn_next_invs_27_37_helper2(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures inv31(dvn') 
    ensures inv34(dvn')
    ensures inv35(dvn')
    {       
        lemma_inv31_dvn_next(dvn, e, dvn');  
        lemma_inv34_dvn_next(dvn, e, dvn');  
        lemma_inv35_dvn_next(dvn, e, dvn');  
        // lemma_inv36_dvn_next(dvn, e, dvn');  
        // lemma_inv37_dvn_next(dvn, e, dvn');  
        // IndInv3.lemma_inv_33(dvn, e, dvn');
    }

    lemma lemma_ind_inv_dvn_next_invs_27_37_helper3(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures inv36(dvn') 
    ensures inv37(dvn')
    ensures IndInv3.inv33(dvn')
    {               
        lemma_inv36_dvn_next(dvn, e, dvn');  
        lemma_inv37_dvn_next(dvn, e, dvn');  
        IndInv3.lemma_inv_33(dvn, e, dvn');
    }

    lemma lemma_ind_inv_dvn_next_invs_27_37(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures invs_27_37(dvn') 
    {
        lemma_ind_inv_dvn_next_invs_27_37_helper1(dvn, e, dvn');
        lemma_ind_inv_dvn_next_invs_27_37_helper2(dvn, e, dvn');
        lemma_ind_inv_dvn_next_invs_27_37_helper3(dvn, e, dvn');
    }

    lemma lemma_ind_inv_implies_intermediate_steps_helper_1(dvn: DVState)
    requires ind_inv(dvn)
    ensures inv11(dvn)
    ensures inv12(dvn)
    ensures inv14(dvn)
    ensures inv15(dvn)
    ensures inv24(dvn)    
    {    
        lemma_inv11_ind_inv(dvn);
        lemma_inv12_ind_inv(dvn);
        lemma_inv14_ind_inv(dvn);
        lemma_inv15_ind_inv(dvn);
        lemma_inv24_ind_inv(dvn);  
    }

    lemma lemma_ind_inv_implies_intermediate_steps_helper_2(dvn: DVState)
    requires ind_inv(dvn)  
    ensures inv50(dvn)
    ensures inv51(dvn)   
    ensures inv53(dvn)    
    ensures construct_signed_attestation_signature_assumptions_helper(
                dvn.construct_signed_attestation_signature,
                dvn.dv_pubkey,
                dvn.all_nodes)  
    {    
        lemma_inv50_ind_inv(dvn);
        lemma_inv51_ind_inv(dvn);
        lemma_inv53_ind_inv(dvn);      
        lemma_construct_signed_attestation_signature_assumptions_helper(dvn);       
    }

    lemma lemma_ind_inv_implies_intermediate_steps_helper_3(dvn: DVState)
    requires ind_inv(dvn)  
    ensures inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(dvn)  
    ensures is_sequence_attestation_duties_to_be_served_orderd(dvn)
    ensures inv_attestation_duty_queue_is_ordered(dvn)
    ensures inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(dvn)
    ensures pred_inv_current_latest_attestation_duty_match(dvn)
    ensures pred_rcvd_attestation_shares_is_in_all_messages_sent(dvn)
    {    
        lemma_inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(dvn);
        lemma_inv_attestation_duty_queue_is_ordered(dvn);
        lemma_inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(dvn);
        lemma_pred_inv_current_latest_attestation_duty_match(dvn);
        lemma_inv37_pred_rcvd_attestation_shares_is_in_all_messages_sent(dvn);
    }

    lemma lemma_ind_inv_implies_intermediate_steps_helper_4(dvn: DVState)
    requires ind_inv(dvn)  
    ensures lemma_pred_4_1_g_iii_precond(dvn)
    ensures lemma_pred_4_1_b_new_precond(dvn)    
    {   
        lemma_ind_inv_implies_intermediate_steps_helper_1(dvn);
        lemma_ind_inv_implies_intermediate_steps_helper_2(dvn);
        lemma_ind_inv_implies_intermediate_steps_helper_3(dvn);        
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
    ensures inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(dvn)   
    ensures is_sequence_attestation_duties_to_be_served_orderd(dvn)     
    ensures inv_attestation_duty_queue_is_ordered(dvn)
    ensures inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(dvn)
    ensures pred_inv_current_latest_attestation_duty_match(dvn)
    ensures pred_rcvd_attestation_shares_is_in_all_messages_sent(dvn)
    ensures lemma_pred_4_1_g_iii_precond(dvn)
    ensures lemma_pred_4_1_b_new_precond(dvn)
    {   
        lemma_ind_inv_implies_intermediate_steps_helper_1(dvn); 
        lemma_ind_inv_implies_intermediate_steps_helper_2(dvn);
        lemma_ind_inv_implies_intermediate_steps_helper_3(dvn);
        lemma_ind_inv_implies_intermediate_steps_helper_4(dvn);
    }
   
    lemma lemma_ind_inv_dvn_next_inv_46_b(dvn: DVState, e: DV.Event, dvn': DVState)  
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')       
    requires ind_inv(dvn)
    ensures inv46_b(dvn')
    {
        lemma_inv29_inv_attestation_consensus_active_instances_predicate_is_in_att_slashing_db_hist(dvn);
        assert inv_attestation_consensus_active_instances_predicate_is_in_att_slashing_db_hist(dvn);

        lemma_inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(dvn);
        assert inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(dvn);

        lemma_ind_inv_implies_intermediate_steps(dvn);
        assert inv53(dvn);


        assert && inv46_b(dvn)
               && inv1(dvn)
               && inv53(dvn)
               && inv3(dvn)    
               && IndInv3.inv33(dvn)  
               && inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(dvn)
               && inv_attestation_consensus_active_instances_predicate_is_in_att_slashing_db_hist(dvn)
               ;

        lemma_inv46_b(dvn, e, dvn');    
        assert inv46_b(dvn');
    }

    lemma lemma_ind_inv_dvn_next_inv_pred_4_1_b(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
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

        assert  && DV.NextEvent(dvn, e, dvn')
                && pred_4_1_b(dvn)
                && construct_signed_attestation_signature_assumptions_helper(
                    dvn.construct_signed_attestation_signature,
                    dvn.dv_pubkey,
                    dvn.all_nodes
                )
                && inv3(dvn)  
                && invNetwork(dvn)
                && inv1(dvn)
                && pred_rcvd_attestation_shares_is_in_all_messages_sent(dvn)
                ;

        
        lemma_pred_4_1_b(dvn, e, dvn');
        assert pred_4_1_b(dvn');
    }

    lemma lemma_ind_inv_dvn_next_inv_pred_4_1_f_a(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures pred_4_1_f_a(dvn')
    {
        lemma_pred_4_1_f_a(dvn, e, dvn');
    }

    lemma lemma_ind_inv_dvn_next_inv_pred_4_1_g_i_for_dvc(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures pred_4_1_g_i_for_dvc(dvn')
    {
        lemma_pred_4_1_f_g_for_dvc(dvn, e, dvn');
    }

    lemma lemma_ind_inv_dvn_next_inv_pred_4_1_g_i(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures pred_4_1_g_i(dvn')
    {
        lemma_pred_4_1_f_g_i(dvn, e, dvn');
    }

    lemma lemma_ind_inv_dvn_next_inv_pred_4_1_f_b(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures pred_4_1_f_b(dvn')
    {
        lemma_pred_4_1_f_b(dvn, e, dvn');
    }

    predicate invs_other_properties_1(dvn: DVState)       
    {                
        && inv46_b(dvn)
        && pred_4_1_b(dvn) 
        && pred_4_1_f_a(dvn)    
        && pred_4_1_g_i_for_dvc(dvn)
        && pred_4_1_g_i(dvn)
        
    }

    lemma lemma_ind_inv_dvn_next_invs_other_properties_1(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures invs_other_properties_1(dvn')
    {
        lemma_ind_inv_dvn_next_inv_46_b(dvn, e, dvn');  
        lemma_ind_inv_dvn_next_inv_pred_4_1_b(dvn, e, dvn');             
        lemma_ind_inv_dvn_next_inv_pred_4_1_f_a(dvn, e, dvn');       
        lemma_ind_inv_dvn_next_inv_pred_4_1_g_i_for_dvc(dvn, e, dvn');  
        lemma_ind_inv_dvn_next_inv_pred_4_1_g_i(dvn, e, dvn');   
    }

    lemma lemma_ind_inv_dvn_next_inv_invNetwork(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures invNetwork(dvn')
    {
        lemma_inv36_dvn_next(dvn, e, dvn');
        lemma_inv36_invNetwork(dvn');
    }

    lemma lemma_ind_inv_dvn_next_inv_38(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures inv38(dvn')
    {
        lemma_ind_inv_implies_intermediate_steps(dvn);
        assert inv53(dvn);
        lemma_inv38_dvn_next(dvn, e, dvn');
    }

    lemma lemma_ind_inv_dvn_next_inv_pred_4_1_g_iii_a(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures pred_4_1_g_iii_a(dvn')
    {
        lemma_pred_4_1_g_iii_a(dvn, e, dvn');
    }

    predicate invs_other_properties_2(dvn: DVState)       
    {                    
        && pred_4_1_f_b(dvn) 
        && invNetwork(dvn)
        && inv38(dvn)
        && inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(dvn)
    }

    lemma lemma_ind_inv_dvn_next_invs_other_properties_2(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures invs_other_properties_2(dvn')
    {
        lemma_pred_4_1_f_b(dvn, e, dvn');
        lemma_ind_inv_dvn_next_inv_invNetwork(dvn, e, dvn');
        lemma_ind_inv_dvn_next_inv_38(dvn, e, dvn');
        lemma_inv38_inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(dvn');
    }

    lemma lemma_pred_4_1_g_iii_ind_inv(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )
    requires NextEvent.requires(dvn, event, dvn')
    requires NextEvent(dvn, event, dvn')
    requires ind_inv(dvn)
    ensures pred_4_1_g_iii(dvn')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dvn);
        assert lemma_pred_4_1_g_iii_precond(dvn);
        lemma_pred_4_1_g_iii(dvn, event, dvn');
    }

    predicate invs_other_properties_3(dvn: DVState)       
    {                
        && pred_4_1_g_iii_a(dvn)        
        && pred_4_1_g_iii_c(dvn)
        && pred_4_1_g_iii_a_a(dvn)        
        && pred_4_1_c(dvn)                     
    }
    
    lemma lemma_ind_inv_dvn_next_invs_other_properties_3(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures invs_other_properties_3(dvn')
    {        
        lemma_ind_inv_dvn_next_inv_pred_4_1_g_iii_a(dvn, e, dvn');
        lemma_pred_4_1_g_iii_c_dvn_next(dvn, e, dvn');
        lemma_pred_4_1_g_iii_a_a(dvn, e, dvn');
        lemma_ind_inv_implies_intermediate_steps(dvn);
        lemma_pred_4_1_c(dvn, e, dvn');
    }
    
    predicate invs_other_properties_4(dvn: DVState)       
    {
        && inv_attestation_duty_queue_is_ordered_3(dvn)
        && inv_attestation_duty_queue_is_ordered_4(dvn)
    }

    lemma lemma_ind_inv_dvn_next_invs_other_properties_4(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures invs_other_properties_4(dvn')
    {        
        lemma_inv_attestation_duty_queue_is_ordered_3(dvn, e, dvn');
        lemma_inv_attestation_duty_queue_is_ordered_4(dvn, e, dvn');        
    }

    lemma lemma_ind_inv_dvn_next_inv_pred_4_1_g_iii_b(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures pred_4_1_g_iii_b(dvn')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dvn);
        lemma_4_1_g_iii_b(dvn, e, dvn');
    }

    lemma lemma_ind_inv_dvn_next_inv_pred_4_1_g_b_new(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures pred_4_1_g_b_new(dvn')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dvn);
        lemma_pred_4_1_b_new(dvn, e, dvn');
    }

    lemma lemma_ind_inv_dvn_next_inv_g_d_a(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures inv_g_d_a(dvn')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dvn);
        lemma_inv_g_d_a(dvn, e, dvn');
    }

    lemma lemma_ind_inv_dvn_next_inv_g_d_b(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures inv_g_d_b(dvn')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dvn);
        lemma_inv_g_d_b(dvn, e, dvn');
    }

    lemma lemma_ind_inv_dvn_next_inv_g_a_ii_a(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures inv_g_a_ii_a(dvn')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dvn);
        lemma_inv_g_a_ii_a(dvn, e, dvn');
    }



    lemma lemma_ind_inv_dvn_next_invs_other_properties_5(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures invs_other_properties_5(dvn')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dvn);
        
        lemma_4_1_g_iii_b(dvn, e, dvn');
        lemma_pred_4_1_b_new(dvn, e, dvn');
        lemma_inv_g_d_a(dvn, e, dvn');
        lemma_inv_g_d_b(dvn, e, dvn');        
        lemma_inv_g_a_ii_a(dvn, e, dvn');
    }

    
    predicate invs_other_properties_5(dvn: DVState)       
    {                
        && pred_4_1_g_iii_b(dvn)    
        && pred_4_1_g_b_new(dvn)    
        && inv_g_d_a(dvn)
        && inv_g_d_b(dvn)  
        && inv_g_a_ii_a(dvn)        
    }
    
    predicate invs_other_properties_6(dvn: DVState)       
    {                
        && inv_g_a_iii(dvn)
        && inv_g_a_iv_a(dvn)
        && pred_4_1_g_iii(dvn)        
    }

    predicate invs_other_properties_7(dvn: DVState)       
    {                
        && inv46_a(dvn)
        && inv46_b(dvn)
    }

          
    lemma lemma_ind_inv_dvn_next_invs_other_properties_6(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures invs_other_properties_6(dvn')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dvn);

        lemma_inv_g_a_iii(dvn, e, dvn');
        lemma_inv_g_a_iv_a(dvn, e, dvn');
        lemma_pred_4_1_g_iii(dvn, e, dvn');        
    }

    lemma lemma_ind_inv_dvn_next_invs_other_properties_7(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures invs_other_properties_7(dvn')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dvn);

        lemma_inv_46_a(dvn, e, dvn');
        lemma_inv46_b(dvn, e, dvn');
    }


    // Adding DV.NextEventPreCond(dvn, e) makes this lemma too complicated for Dafny on my computer.
    // lemma lemma_ind_inv_dvn_next_ind_inv_helper_1(dvn: DVState, e: DV.Event, dvn': DVState)       
    // requires DV.NextEventPreCond(dvn, e)
    // requires DV.NextEvent(dvn, e, dvn')  
    // requires ind_inv(dvn)
    // ensures invs_1_7(dvn')
    // ensures invs_8_18(dvn')
    // ensures invs_19_26(dvn')
    // ensures invs_27_37(dvn')
    // {
    //     lemma_ind_inv_dvn_next_invs_1_7(dvn, e, dvn');
    //     lemma_ind_inv_dvn_next_invs_8_18(dvn, e, dvn');
    //     lemma_ind_inv_dvn_next_invs_19_26(dvn, e, dvn');
    //     lemma_ind_inv_dvn_next_invs_27_37(dvn, e, dvn');         
    // }
    
    lemma lemma_ind_inv_dvn_next_ind_inv_helper_1(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures invs_1_7(dvn')
    ensures invs_8_18(dvn')
    {
        lemma_ind_inv_dvn_next_invs_1_7(dvn, e, dvn');
        lemma_ind_inv_dvn_next_invs_8_18(dvn, e, dvn');
    }

    lemma lemma_ind_inv_dvn_next_ind_inv_helper_2(dvn: DVState, e: DV.Event, dvn': DVState)  
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)    
    ensures invs_19_26(dvn')
    ensures invs_27_37(dvn')     
    {
        lemma_ind_inv_dvn_next_invs_19_26(dvn, e, dvn');
        lemma_ind_inv_dvn_next_invs_27_37(dvn, e, dvn');
    }

    lemma lemma_ind_inv_dvn_next_ind_inv_helper_3(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)
    ensures invs_other_properties_1(dvn')
    ensures invs_other_properties_2(dvn')
    ensures invs_other_properties_3(dvn')
    ensures invs_other_properties_4(dvn')    
    {        
        lemma_ind_inv_dvn_next_invs_other_properties_1(dvn, e, dvn');       
        lemma_ind_inv_dvn_next_invs_other_properties_2(dvn, e, dvn');  
        lemma_ind_inv_dvn_next_invs_other_properties_3(dvn, e, dvn');            
        lemma_ind_inv_dvn_next_invs_other_properties_4(dvn, e, dvn');                              
    }

    lemma lemma_ind_inv_dvn_next_ind_inv_helper_4(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)    
    ensures invs_other_properties_5(dvn')
    ensures invs_other_properties_6(dvn')
    ensures invs_other_properties_7(dvn')
    {                 
        lemma_ind_inv_dvn_next_invs_other_properties_5(dvn, e, dvn');            
        lemma_ind_inv_dvn_next_invs_other_properties_6(dvn, e, dvn');            
        lemma_ind_inv_dvn_next_invs_other_properties_7(dvn, e, dvn');            
    }

    lemma lemma_ind_inv_dvn_next_ind_inv_helper_a(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn) 
    ensures invs_1_7(dvn')
    ensures invs_8_18(dvn')   
    ensures invs_19_26(dvn')
    ensures invs_27_37(dvn')  
    {
        lemma_ind_inv_dvn_next_ind_inv_helper_1(dvn, e, dvn');                          
        lemma_ind_inv_dvn_next_ind_inv_helper_2(dvn, e, dvn');    
    }

    lemma lemma_ind_inv_dvn_next_ind_inv_helper_b(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn) 
    ensures invs_other_properties_1(dvn')    
    ensures invs_other_properties_2(dvn')    
    ensures invs_other_properties_3(dvn')    
    ensures invs_other_properties_4(dvn')    
    ensures invs_other_properties_5(dvn')    
    ensures invs_other_properties_6(dvn')  
    ensures invs_other_properties_7(dvn')  
    {
        lemma_ind_inv_dvn_next_ind_inv_helper_3(dvn, e, dvn');     
        lemma_ind_inv_dvn_next_ind_inv_helper_4(dvn, e, dvn');            
    }

    lemma lemma_ind_inv_dvn_next_ind_inv_helper(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn) 
    ensures invs_1_7(dvn')
    ensures invs_8_18(dvn')   
    ensures invs_19_26(dvn')
    ensures invs_27_37(dvn')  
    ensures invs_other_properties_1(dvn')    
    ensures invs_other_properties_2(dvn')    
    ensures invs_other_properties_3(dvn')    
    ensures invs_other_properties_4(dvn')    
    ensures invs_other_properties_5(dvn')    
    ensures invs_other_properties_6(dvn')    
    ensures invs_other_properties_7(dvn')    
    {   
        lemma_ind_inv_dvn_next_ind_inv_helper_a(dvn, e, dvn');
        lemma_ind_inv_dvn_next_ind_inv_helper_b(dvn, e, dvn');                
    }

    lemma lemma_ind_inv_dvn_next_ind_inv(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEventPreCond(dvn, e)
    requires DV.NextEvent(dvn, e, dvn')  
    requires ind_inv(dvn)    
    ensures ind_inv(dvn')    
    {   
        lemma_ind_inv_dvn_next_ind_inv_helper(dvn, e, dvn');                          
        lemma_inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_next_honest(dvn, e, dvn');       
    }

    lemma lemma_ind_inv_dvn_ind(dvn: DVState, dvn': DVState)       
    requires DV.NextPreCond(dvn)
    requires DV.Next(dvn, dvn')  
    requires ind_inv(dvn)    
    ensures ind_inv(dvn')  
    ensures DV.NextPreCond(dvn')
    {
        var e :|
            && validEvent(dvn, e)
            && NextEvent(dvn, e, dvn');

        lemma_ind_inv_dvn_next_ind_inv(dvn, e, dvn');
        lemma_NextPreCond(dvn');
    }      

    predicate non_slashable_attestations(
        dvn: DVState
    )
    {
        forall a: Attestation, a': Attestation
                | 
                && a in dvn.all_attestations_created
                && is_valid_attestation(a, dvn.dv_pubkey)
                && a' in dvn.all_attestations_created
                && is_valid_attestation(a', dvn.dv_pubkey)     
                ::
                && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
                && !is_slashable_attestation_data_eth_spec(a'.data, a.data)
    }

    lemma lemma_ind_inv_4_1_general(dvn: DVState)
    requires ind_inv(dvn)    
    ensures non_slashable_attestations(dvn)
    {   
        lemma_ind_inv_implies_intermediate_steps(dvn);

        forall a: Attestation, a': Attestation
                    | 
                    && a in dvn.all_attestations_created
                    && is_valid_attestation(a, dvn.dv_pubkey)
                    && a' in dvn.all_attestations_created
                    && is_valid_attestation(a', dvn.dv_pubkey)     
        ensures && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
                && !is_slashable_attestation_data_eth_spec(a'.data, a.data);
        {
            assert 
            && inv1(dvn)
            && inv2(dvn)
            && pred_4_1_b(dvn)
            && pred_4_1_c(dvn)
            && pred_4_1_f_a(dvn)    
            && pred_4_1_g_i(dvn)
            && pred_4_1_g_iii(dvn)
            && a in dvn.all_attestations_created
            && is_valid_attestation(a, dvn.dv_pubkey)
            && a' in dvn.all_attestations_created
            && is_valid_attestation(a', dvn.dv_pubkey)
            && inv46_a(dvn)
            && inv46_b(dvn)
            && inv50(dvn)
            && inv51(dvn)
            ;
            lemma_4_1_general(dvn, a, a');
        }
    }

    predicate isValidTrace(
        trace: iseq<DVState>
    )  
    {
        && DV.Init(trace[0], {})
        && (
            forall i: nat ::
                DV.NextPreCond(trace[i]) ==> DV.Next(trace[i], trace[i+1])
        )
    }  

    lemma lemma_non_slashable_attestations_rec(
        trace: iseq<DVState>,
        i: nat
    )
    requires isValidTrace(trace)
    ensures forall j | 0 <= j <= i ::
        && NextPreCond(trace[j])  
        && ind_inv(trace[j])
    {
        if i == 0 
        {
            lemma_ind_inv_dvn_init(trace[0]);
        }
        else 
        {
            lemma_non_slashable_attestations_rec(trace, i-1);
            lemma_ind_inv_dvn_ind(trace[i-1], trace[i]);
        }
    }

    lemma lemma_non_slashable_attestations(
        trace: iseq<DVState>
    )
    requires isValidTrace(trace)
    ensures forall i:nat :: non_slashable_attestations(trace[i])
    {
        forall i:nat
        ensures ind_inv(trace[i])
        ensures non_slashable_attestations(trace[i])
        {
            lemma_non_slashable_attestations_rec(trace, i);
            lemma_ind_inv_4_1_general(trace[i]);
        }
        
    }    

}