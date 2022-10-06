include "../../../common/commons.dfy"
include "../common/attestation_creation_instrumented.dfy"
include "../../../specs/consensus/consensus.dfy"
include "../../../specs/network/network.dfy"
include "../../../specs/dv/dv_attestation_creation.dfy"
include "inv.dfy"
include "fnc_invs_1_26.dfy"
include "../../common/helper_sets_lemmas.dfy"
include "proofs_intermediate_steps.dfy"
include "dv_next_invs_1_7.dfy"
include "dv_next_invs_8_18.dfy"
include "dv_next_invs_19_26.dfy"
include "dv_next_invs_27_37.dfy"
include "ind_inv.dfy"
include "ind_inv2.dfy"
include "ind_inv3.dfy"
include "ind_inv4.dfy"
include "core_proofs.dfy"


module Proofs_DV_Ind_Inv
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Att_Ind_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Att_Ind_Inv_With_Empty_Initial_Attestation_Slashing_DB2
    import opened Fnc_Invs_1_26
    import opened Helper_Sets_Lemmas
    import opened DV_Next_Invs_1_7
    import opened DV_Next_Invs_8_18
    import opened DV_Next_Invs_19_26
    import opened Proofs_Intermediate_Steps
    import opened DV_Next_Invs_27_37
    import opened Core_Proofs
    import opened IndInv3
    import opened IndInv4

    predicate ind_inv(dv: DVState)       
    {
        && invs_1_7(dv)
        && invs_8_18(dv)
        && invs_19_26(dv)
        && invs_27_37(dv)
        && invs_other_properties_1(dv)
        && invs_other_properties_2(dv)
        && invs_other_properties_3(dv)
        && invs_other_properties_4(dv)
        && invs_other_properties_5(dv)
        && invs_other_properties_6(dv)
        && invs_other_properties_7(dv)
        && inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue(dv)
    }

    predicate invs_1_7(dv: DVState)       
    {
        &&  quorum_constraints(dv)
        &&  unchanged_honesty(dv)
        &&  only_dv_construct_signed_attestation_signature(dv)
        &&  inv4(dv)
        &&  inv5(dv)
        &&  inv6(dv)
        &&  inv7(dv)
    }

    predicate invs_8_18(dv: DVState)       
    {        
        &&  inv8(dv)   
        &&  inv9(dv)  
        &&  inv10(dv) 
        &&  inv13(dv)      
        &&  inv16(dv)  
        &&  inv17(dv)  
        &&  inv18(dv)  
    }
    
    predicate invs_19_26(dv: DVState)       
    {        
        &&  inv19(dv)           
        &&  inv21(dv) 
        &&  inv22(dv)      
        &&  inv23(dv)  
        &&  inv25(dv)          
        &&  inv26(dv)  
    }

    predicate invs_27_37(dv: DVState)       
    {                
        &&  inv27(dv)  
        &&  inv28(dv)  
        &&  inv29(dv)  
        &&  inv31(dv)  
        &&  inv34(dv)
        &&  inv35(dv)
        &&  inv36(dv)
        &&  inv37(dv)
        &&  IndInv3.inv33(dv)
    }


    
    lemma lemma_ind_inv_dv_init(dv: DVState)       
    requires DV.Init(dv, {})    
    ensures ind_inv(dv)
    ensures NextPreCond(dv)
    {
        assert  DV.Init(dv, {})  
                ==>                 
                && invs_1_7(dv)
                && invs_8_18(dv)
                && invs_19_26(dv)
                && invs_27_37(dv);

        assert  DV.Init(dv, {})    
                ==>
                && invs_other_properties_1(dv)
                && invs_other_properties_2(dv)
                && invs_other_properties_3(dv)
                && invs_other_properties_4(dv)
                && invs_other_properties_5(dv)
                && invs_other_properties_6(dv)
                ;
    }  

    

    

    lemma lemma_ind_inv_dv_next_invs_1_7(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_1_7(dv')
    {    
        lemma_quorum_constraints_dv_next(dv, e, dv');
        lemma_unchanged_honesty_dv_next(dv, e, dv');
        lemma_only_dv_construct_signed_attestation_signature_dv_next(dv, e, dv');
        lemma_inv4_dv_next(dv, e, dv');
        lemma_inv5_dv_next(dv, e, dv');
        lemma_inv6_dv_next(dv, e, dv');
        lemma_inv7_dv_next(dv, e, dv');        
    }

    lemma lemma_ind_inv_dv_next_invs_8_18_helper_1(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv8(dv')
    ensures inv9(dv')
    ensures inv10(dv')
    ensures inv13(dv')
    {
        lemma_inv8_dv_next(dv, e, dv');
        lemma_inv9_dv_next(dv, e, dv');
        lemma_inv10_dv_next(dv, e, dv');        
        lemma_inv13_dv_next(dv, e, dv');                
        // lemma_inv16_dv_next(dv, e, dv');
        // lemma_inv17_dv_next(dv, e, dv');
        // lemma_inv18_dv_next(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_invs_8_18_helper_2(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv16(dv')
    ensures inv17(dv')
    ensures inv18(dv')
    {
        lemma_inv16_dv_next(dv, e, dv');
        lemma_inv17_dv_next(dv, e, dv');
        lemma_inv18_dv_next(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_invs_8_18(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_8_18(dv')
    {
        lemma_ind_inv_dv_next_invs_8_18_helper_1(dv, e, dv');
        lemma_ind_inv_dv_next_invs_8_18_helper_2(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_invs_19_26_helper_1(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv19(dv')        
    ensures inv20(dv, dv')
    ensures inv21(dv')
    ensures inv22(dv')
    {
        lemma_inv19_dv_next(dv, e, dv');
        lemma_inv20_dv_next(dv, e, dv');
        lemma_inv21_dv_next(dv, e, dv');        
        lemma_inv22_dv_next(dv, e, dv');                
        // lemma_inv23_dv_next(dv, e, dv');                
        // lemma_inv25_dv_next(dv, e, dv');    
        // lemma_inv26_dv_next(dv, e, dv');    
    }

    lemma lemma_ind_inv_dv_next_invs_19_26_helper_2(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv23(dv')        
    ensures inv25(dv')
    ensures inv26(dv')
    {
        lemma_inv23_dv_next(dv, e, dv');                
        lemma_inv25_dv_next(dv, e, dv');    
        lemma_inv26_dv_next(dv, e, dv');    
    }

    lemma lemma_ind_inv_dv_next_invs_19_26(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_19_26(dv')        
    {
        lemma_ind_inv_dv_next_invs_19_26_helper_1(dv, e, dv');
        lemma_ind_inv_dv_next_invs_19_26_helper_2(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_invs_27_37_helper1(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv27(dv') 
    ensures inv28(dv')
    ensures inv29(dv')
    {
        lemma_inv27_dv_next(dv, e, dv');    
        lemma_inv28_dv_next(dv, e, dv');  
        lemma_inv29_dv_next(dv, e, dv');          
    }

    lemma lemma_ind_inv_dv_next_invs_27_37_helper2(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv31(dv') 
    ensures inv34(dv')
    ensures inv35(dv')
    {       
        lemma_inv31_dv_next(dv, e, dv');  
        lemma_inv34_dv_next(dv, e, dv');  
        lemma_inv35_dv_next(dv, e, dv');  
        // lemma_inv36_dv_next(dv, e, dv');  
        // lemma_inv37_dv_next(dv, e, dv');  
        // IndInv3.lemma_inv_33(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_invs_27_37_helper3(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv36(dv') 
    ensures inv37(dv')
    ensures IndInv3.inv33(dv')
    {               
        lemma_inv36_dv_next(dv, e, dv');  
        lemma_inv37_dv_next(dv, e, dv');  
        IndInv3.lemma_inv_33(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_invs_27_37(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_27_37(dv') 
    {
        lemma_ind_inv_dv_next_invs_27_37_helper1(dv, e, dv');
        lemma_ind_inv_dv_next_invs_27_37_helper2(dv, e, dv');
        lemma_ind_inv_dv_next_invs_27_37_helper3(dv, e, dv');
    }

    lemma lemma_ind_inv_implies_intermediate_steps_helper_1(dv: DVState)
    requires ind_inv(dv)
    ensures inv11(dv)
    ensures inv12(dv)
    ensures inv14(dv)
    ensures inv15(dv)
    ensures inv24(dv)    
    {    
        lemma_inv11_ind_inv(dv);
        lemma_inv12_ind_inv(dv);
        lemma_inv14_ind_inv(dv);
        lemma_inv15_ind_inv(dv);
        lemma_inv24_ind_inv(dv);  
    }

    lemma lemma_ind_inv_implies_intermediate_steps_helper_2(dv: DVState)
    requires ind_inv(dv)  
    ensures inv50(dv)
    ensures inv51(dv)   
    ensures inv53(dv)    
    ensures construct_signed_attestation_signature_assumptions_helper(
                dv.construct_signed_attestation_signature,
                dv.dv_pubkey,
                dv.all_nodes)  
    {    
        lemma_inv50_ind_inv(dv);
        lemma_inv51_ind_inv(dv);
        lemma_inv53_ind_inv(dv);      
        lemma_construct_signed_attestation_signature_assumptions_helper(dv);       
    }

    lemma lemma_ind_inv_implies_intermediate_steps_helper_3(dv: DVState)
    requires ind_inv(dv)  
    ensures inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(dv)  
    ensures is_sequence_attestation_duties_to_be_served_orderd(dv)
    ensures inv_attestation_duty_queue_is_ordered(dv)
    ensures inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(dv)
    ensures pred_inv_current_latest_attestation_duty_match(dv)
    ensures pred_rcvd_attestation_shares_is_in_all_messages_sent(dv)
    {    
        lemma_inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(dv);
        lemma_inv_attestation_duty_queue_is_ordered(dv);
        lemma_inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(dv);
        lemma_pred_inv_current_latest_attestation_duty_match(dv);
        lemma_inv37_pred_rcvd_attestation_shares_is_in_all_messages_sent(dv);
    }

    lemma lemma_ind_inv_implies_intermediate_steps_helper_4(dv: DVState)
    requires ind_inv(dv)  
    ensures lemma_pred_4_1_g_iii_precond(dv)
    ensures lemma_pred_4_1_b_new_precond(dv)    
    {   
        lemma_ind_inv_implies_intermediate_steps_helper_1(dv);
        lemma_ind_inv_implies_intermediate_steps_helper_2(dv);
        lemma_ind_inv_implies_intermediate_steps_helper_3(dv);        
    }

    lemma lemma_ind_inv_implies_intermediate_steps(dv: DVState)
    requires ind_inv(dv)
    ensures inv11(dv)
    ensures inv12(dv)
    ensures inv14(dv)
    ensures inv15(dv)
    ensures inv24(dv)    
    ensures inv50(dv)
    ensures inv51(dv)   
    ensures inv53(dv)    
    ensures construct_signed_attestation_signature_assumptions_helper(
                dv.construct_signed_attestation_signature,
                dv.dv_pubkey,
                dv.all_nodes)  
    ensures inv_head_attetation_duty_queue_higher_than_latest_attestation_duty(dv)   
    ensures is_sequence_attestation_duties_to_be_served_orderd(dv)     
    ensures inv_attestation_duty_queue_is_ordered(dv)
    ensures inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(dv)
    ensures pred_inv_current_latest_attestation_duty_match(dv)
    ensures pred_rcvd_attestation_shares_is_in_all_messages_sent(dv)
    ensures lemma_pred_4_1_g_iii_precond(dv)
    ensures lemma_pred_4_1_b_new_precond(dv)
    {   
        lemma_ind_inv_implies_intermediate_steps_helper_1(dv); 
        lemma_ind_inv_implies_intermediate_steps_helper_2(dv);
        lemma_ind_inv_implies_intermediate_steps_helper_3(dv);
        lemma_ind_inv_implies_intermediate_steps_helper_4(dv);
    }
   
    lemma lemma_ind_inv_dv_next_inv_46_b(dv: DVState, e: DV.Event, dv': DVState)  
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')       
    requires ind_inv(dv)
    ensures inv46_b(dv')
    {
        lemma_inv29_inv_attestation_consensus_active_instances_predicate_is_in_att_slashing_db_hist(dv);
        assert inv_attestation_consensus_active_instances_predicate_is_in_att_slashing_db_hist(dv);

        lemma_inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(dv);
        assert inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(dv);

        lemma_ind_inv_implies_intermediate_steps(dv);
        assert inv53(dv);


        assert && inv46_b(dv)
               && quorum_constraints(dv)
               && inv53(dv)
               && only_dv_construct_signed_attestation_signature(dv)    
               && IndInv3.inv33(dv)  
               && inv_attestation_consensus_active_instances_keys_is_subset_of_att_slashing_db_hist(dv)
               && inv_attestation_consensus_active_instances_predicate_is_in_att_slashing_db_hist(dv)
               ;

        lemma_inv46_b(dv, e, dv');    
        assert inv46_b(dv');
    }

    lemma lemma_ind_inv_dv_next_inv_pred_4_1_b(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures pred_4_1_b(dv')
    {
        lemma_ind_inv_implies_intermediate_steps(dv);
        assert construct_signed_attestation_signature_assumptions_helper(
                dv.construct_signed_attestation_signature,
                dv.dv_pubkey,
                dv.all_nodes);

        lemma_inv36_invNetwork(dv);
        assert invNetwork(dv);

        lemma_inv37_pred_rcvd_attestation_shares_is_in_all_messages_sent(dv);
        assert pred_rcvd_attestation_shares_is_in_all_messages_sent(dv);

        assert  && DV.NextEvent(dv, e, dv')
                && pred_4_1_b(dv)
                && construct_signed_attestation_signature_assumptions_helper(
                    dv.construct_signed_attestation_signature,
                    dv.dv_pubkey,
                    dv.all_nodes
                )
                && only_dv_construct_signed_attestation_signature(dv)  
                && invNetwork(dv)
                && quorum_constraints(dv)
                && pred_rcvd_attestation_shares_is_in_all_messages_sent(dv)
                ;

        
        lemma_pred_4_1_b(dv, e, dv');
        assert pred_4_1_b(dv');
    }

    lemma lemma_ind_inv_dv_next_inv_pred_4_1_f_a(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures pred_4_1_f_a(dv')
    {
        lemma_pred_4_1_f_a(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_inv_pred_4_1_g_i_for_dvc(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures pred_4_1_g_i_for_dvc(dv')
    {
        lemma_pred_4_1_f_g_for_dvc(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_inv_pred_4_1_g_i(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures pred_4_1_g_i(dv')
    {
        lemma_pred_4_1_f_g_i(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_inv_pred_4_1_f_b(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures pred_4_1_f_b(dv')
    {
        lemma_pred_4_1_f_b(dv, e, dv');
    }

    predicate invs_other_properties_1(dv: DVState)       
    {                
        && inv46_b(dv)
        && pred_4_1_b(dv) 
        && pred_4_1_f_a(dv)    
        && pred_4_1_g_i_for_dvc(dv)
        && pred_4_1_g_i(dv)
        
    }

    lemma lemma_ind_inv_dv_next_invs_other_properties_1(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_other_properties_1(dv')
    {
        lemma_ind_inv_dv_next_inv_46_b(dv, e, dv');  
        lemma_ind_inv_dv_next_inv_pred_4_1_b(dv, e, dv');             
        lemma_ind_inv_dv_next_inv_pred_4_1_f_a(dv, e, dv');       
        lemma_ind_inv_dv_next_inv_pred_4_1_g_i_for_dvc(dv, e, dv');  
        lemma_ind_inv_dv_next_inv_pred_4_1_g_i(dv, e, dv');   
    }

    lemma lemma_ind_inv_dv_next_inv_invNetwork(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invNetwork(dv')
    {
        lemma_inv36_dv_next(dv, e, dv');
        lemma_inv36_invNetwork(dv');
    }

    lemma lemma_ind_inv_dv_next_inv_38(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv38(dv')
    {
        lemma_ind_inv_implies_intermediate_steps(dv);
        assert inv53(dv);
        lemma_inv38_dv_next(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_inv_pred_4_1_g_iii_a(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures pred_4_1_g_iii_a(dv')
    {
        lemma_pred_4_1_g_iii_a(dv, e, dv');
    }

    predicate invs_other_properties_2(dv: DVState)       
    {                    
        && pred_4_1_f_b(dv) 
        && invNetwork(dv)
        && inv38(dv)
        && inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(dv)
    }

    lemma lemma_ind_inv_dv_next_invs_other_properties_2(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_other_properties_2(dv')
    {
        lemma_pred_4_1_f_b(dv, e, dv');
        lemma_ind_inv_dv_next_inv_invNetwork(dv, e, dv');
        lemma_ind_inv_dv_next_inv_38(dv, e, dv');
        lemma_inv38_inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(dv');
    }

    lemma lemma_pred_4_1_g_iii_ind_inv(
        dv: DVState,
        event: DV.Event,
        dv': DVState
    )
    requires NextEvent.requires(dv, event, dv')
    requires NextEvent(dv, event, dv')
    requires ind_inv(dv)
    ensures pred_4_1_g_iii(dv')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dv);
        assert lemma_pred_4_1_g_iii_precond(dv);
        lemma_pred_4_1_g_iii(dv, event, dv');
    }

    predicate invs_other_properties_3(dv: DVState)       
    {                
        && pred_4_1_g_iii_a(dv)        
        && pred_4_1_g_iii_c(dv)
        && pred_4_1_g_iii_a_a(dv)        
        && pred_4_1_c(dv)                     
    }
    
    lemma lemma_ind_inv_dv_next_invs_other_properties_3(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_other_properties_3(dv')
    {        
        lemma_ind_inv_dv_next_inv_pred_4_1_g_iii_a(dv, e, dv');
        lemma_pred_4_1_g_iii_c_dv_next(dv, e, dv');
        lemma_pred_4_1_g_iii_a_a(dv, e, dv');
        lemma_ind_inv_implies_intermediate_steps(dv);
        lemma_pred_4_1_c(dv, e, dv');
    }
    
    predicate invs_other_properties_4(dv: DVState)       
    {
        && inv_attestation_duty_queue_is_ordered_3(dv)
        && inv_attestation_duty_queue_is_ordered_4(dv)
    }

    lemma lemma_ind_inv_dv_next_invs_other_properties_4(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_other_properties_4(dv')
    {        
        lemma_inv_attestation_duty_queue_is_ordered_3(dv, e, dv');
        lemma_inv_attestation_duty_queue_is_ordered_4(dv, e, dv');        
    }

    lemma lemma_ind_inv_dv_next_inv_pred_4_1_g_iii_b(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures pred_4_1_g_iii_b(dv')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dv);
        lemma_4_1_g_iii_b(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_inv_pred_4_1_g_b_new(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures pred_4_1_g_b_new(dv')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dv);
        lemma_pred_4_1_b_new(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_inv_g_d_a(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_g_d_a(dv')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dv);
        lemma_inv_g_d_a(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_inv_g_d_b(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_g_d_b(dv')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dv);
        lemma_inv_g_d_b(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_inv_g_a_ii_a(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures inv_g_a_ii_a(dv')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dv);
        lemma_inv_g_a_ii_a(dv, e, dv');
    }



    lemma lemma_ind_inv_dv_next_invs_other_properties_5(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_other_properties_5(dv')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dv);
        
        lemma_4_1_g_iii_b(dv, e, dv');
        lemma_pred_4_1_b_new(dv, e, dv');
        lemma_inv_g_d_a(dv, e, dv');
        lemma_inv_g_d_b(dv, e, dv');        
        lemma_inv_g_a_ii_a(dv, e, dv');
    }

    
    predicate invs_other_properties_5(dv: DVState)       
    {                
        && pred_4_1_g_iii_b(dv)    
        && pred_4_1_g_b_new(dv)    
        && inv_g_d_a(dv)
        && inv_g_d_b(dv)  
        && inv_g_a_ii_a(dv)        
    }
    
    predicate invs_other_properties_6(dv: DVState)       
    {                
        && inv_g_a_iii(dv)
        && inv_g_a_iv_a(dv)
        && pred_4_1_g_iii(dv)        
    }

    predicate invs_other_properties_7(dv: DVState)       
    {                
        && inv46_a(dv)
        && inv46_b(dv)
    }

          
    lemma lemma_ind_inv_dv_next_invs_other_properties_6(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_other_properties_6(dv')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dv);

        lemma_inv_g_a_iii(dv, e, dv');
        lemma_inv_g_a_iv_a(dv, e, dv');
        lemma_pred_4_1_g_iii(dv, e, dv');        
    }

    lemma lemma_ind_inv_dv_next_invs_other_properties_7(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_other_properties_7(dv')
    {
        lemma_ind_inv_implies_intermediate_steps_helper_4(dv);

        lemma_inv_46_a(dv, e, dv');
        lemma_inv46_b(dv, e, dv');
    }


    // Adding DV.NextEventPreCond(dv, e) makes this lemma too complicated for Dafny on my computer.
    // lemma lemma_ind_inv_dv_next_ind_inv_helper_1(dv: DVState, e: DV.Event, dv': DVState)       
    // requires DV.NextEventPreCond(dv, e)
    // requires DV.NextEvent(dv, e, dv')  
    // requires ind_inv(dv)
    // ensures invs_1_7(dv')
    // ensures invs_8_18(dv')
    // ensures invs_19_26(dv')
    // ensures invs_27_37(dv')
    // {
    //     lemma_ind_inv_dv_next_invs_1_7(dv, e, dv');
    //     lemma_ind_inv_dv_next_invs_8_18(dv, e, dv');
    //     lemma_ind_inv_dv_next_invs_19_26(dv, e, dv');
    //     lemma_ind_inv_dv_next_invs_27_37(dv, e, dv');         
    // }
    
    lemma lemma_ind_inv_dv_next_ind_inv_helper_1(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_1_7(dv')
    ensures invs_8_18(dv')
    {
        lemma_ind_inv_dv_next_invs_1_7(dv, e, dv');
        lemma_ind_inv_dv_next_invs_8_18(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_ind_inv_helper_2(dv: DVState, e: DV.Event, dv': DVState)  
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)    
    ensures invs_19_26(dv')
    ensures invs_27_37(dv')     
    {
        lemma_ind_inv_dv_next_invs_19_26(dv, e, dv');
        lemma_ind_inv_dv_next_invs_27_37(dv, e, dv');
    }

    lemma lemma_ind_inv_dv_next_ind_inv_helper_3(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)
    ensures invs_other_properties_1(dv')
    ensures invs_other_properties_2(dv')
    ensures invs_other_properties_3(dv')
    ensures invs_other_properties_4(dv')    
    {        
        lemma_ind_inv_dv_next_invs_other_properties_1(dv, e, dv');       
        lemma_ind_inv_dv_next_invs_other_properties_2(dv, e, dv');  
        lemma_ind_inv_dv_next_invs_other_properties_3(dv, e, dv');            
        lemma_ind_inv_dv_next_invs_other_properties_4(dv, e, dv');                              
    }

    lemma lemma_ind_inv_dv_next_ind_inv_helper_4(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)    
    ensures invs_other_properties_5(dv')
    ensures invs_other_properties_6(dv')
    ensures invs_other_properties_7(dv')
    {                 
        lemma_ind_inv_dv_next_invs_other_properties_5(dv, e, dv');            
        lemma_ind_inv_dv_next_invs_other_properties_6(dv, e, dv');            
        lemma_ind_inv_dv_next_invs_other_properties_7(dv, e, dv');            
    }

    lemma lemma_ind_inv_dv_next_ind_inv_helper_a(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv) 
    ensures invs_1_7(dv')
    ensures invs_8_18(dv')   
    ensures invs_19_26(dv')
    ensures invs_27_37(dv')  
    {
        lemma_ind_inv_dv_next_ind_inv_helper_1(dv, e, dv');                          
        lemma_ind_inv_dv_next_ind_inv_helper_2(dv, e, dv');    
    }

    lemma lemma_ind_inv_dv_next_ind_inv_helper_b(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv) 
    ensures invs_other_properties_1(dv')    
    ensures invs_other_properties_2(dv')    
    ensures invs_other_properties_3(dv')    
    ensures invs_other_properties_4(dv')    
    ensures invs_other_properties_5(dv')    
    ensures invs_other_properties_6(dv')  
    ensures invs_other_properties_7(dv')  
    {
        lemma_ind_inv_dv_next_ind_inv_helper_3(dv, e, dv');     
        lemma_ind_inv_dv_next_ind_inv_helper_4(dv, e, dv');            
    }

    lemma lemma_ind_inv_dv_next_ind_inv_helper(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv) 
    ensures invs_1_7(dv')
    ensures invs_8_18(dv')   
    ensures invs_19_26(dv')
    ensures invs_27_37(dv')  
    ensures invs_other_properties_1(dv')    
    ensures invs_other_properties_2(dv')    
    ensures invs_other_properties_3(dv')    
    ensures invs_other_properties_4(dv')    
    ensures invs_other_properties_5(dv')    
    ensures invs_other_properties_6(dv')    
    ensures invs_other_properties_7(dv')    
    {   
        lemma_ind_inv_dv_next_ind_inv_helper_a(dv, e, dv');
        lemma_ind_inv_dv_next_ind_inv_helper_b(dv, e, dv');                
    }

    lemma lemma_ind_inv_dv_next_ind_inv(dv: DVState, e: DV.Event, dv': DVState)       
    requires DV.NextEventPreCond(dv, e)
    requires DV.NextEvent(dv, e, dv')  
    requires ind_inv(dv)    
    ensures ind_inv(dv')    
    {   
        lemma_ind_inv_dv_next_ind_inv_helper(dv, e, dv');                          
        lemma_inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_next_honest(dv, e, dv');       
    }

    lemma lemma_ind_inv_dv_ind(dv: DVState, dv': DVState)       
    requires DV.NextPreCond(dv)
    requires DV.Next(dv, dv')  
    requires ind_inv(dv)    
    ensures ind_inv(dv')  
    ensures DV.NextPreCond(dv')
    {
        var e :|
            && validEvent(dv, e)
            && NextEvent(dv, e, dv');

        lemma_ind_inv_dv_next_ind_inv(dv, e, dv');
        lemma_NextPreCond(dv');
    }      

    predicate non_slashable_attestations(
        dv: DVState
    )
    {
        forall a: Attestation, a': Attestation
                | 
                && a in dv.all_attestations_created
                && is_valid_attestation(a, dv.dv_pubkey)
                && a' in dv.all_attestations_created
                && is_valid_attestation(a', dv.dv_pubkey)     
                ::
                && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
                && !is_slashable_attestation_data_eth_spec(a'.data, a.data)
    }

    lemma lemma_ind_inv_4_1_general(dv: DVState)
    requires ind_inv(dv)    
    ensures non_slashable_attestations(dv)
    {   
        lemma_ind_inv_implies_intermediate_steps(dv);

        forall a: Attestation, a': Attestation
                    | 
                    && a in dv.all_attestations_created
                    && is_valid_attestation(a, dv.dv_pubkey)
                    && a' in dv.all_attestations_created
                    && is_valid_attestation(a', dv.dv_pubkey)     
        ensures && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
                && !is_slashable_attestation_data_eth_spec(a'.data, a.data);
        {
            assert 
            && quorum_constraints(dv)
            && unchanged_honesty(dv)
            && pred_4_1_b(dv)
            && pred_4_1_c(dv)
            && pred_4_1_f_a(dv)    
            && pred_4_1_g_i(dv)
            && pred_4_1_g_iii(dv)
            && a in dv.all_attestations_created
            && is_valid_attestation(a, dv.dv_pubkey)
            && a' in dv.all_attestations_created
            && is_valid_attestation(a', dv.dv_pubkey)
            && inv46_a(dv)
            && inv46_b(dv)
            && inv50(dv)
            && inv51(dv)
            ;
            lemma_4_1_general(dv, a, a');
        }
    }

}