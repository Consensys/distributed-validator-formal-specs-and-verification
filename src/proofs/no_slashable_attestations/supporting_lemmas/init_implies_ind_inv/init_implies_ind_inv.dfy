include "../../../../common/commons.dfy"
include "../../common/attestation_creation_instrumented.dfy"
include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_attestation_creation.dfy"
include "../inv.dfy"
include "../ind_inv.dfy"

module Ind_Inv_DV_Init
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Spec
    import opened DV
    import opened Att_Ind_Inv_With_Empty_Init_Att_Slashing_DB
    
    lemma lem_ind_inv_dv_init(dv: DVState)       
    requires DV.Init(dv, {})    
    ensures ind_inv(dv)
    ensures NextPreCond(dv)
    {
        assert  DV.Init(dv, {})  
                ==>                 
                && invs_group_1(dv)
                && invs_group_2(dv)
                && invs_group_3(dv)                
                && invs_group_4(dv)
                && invs_group_5(dv)   
                && invs_group_6(dv)                
                && invs_group_7(dv)
                && invs_group_8(dv)                
        ;

        assert  DV.Init(dv, {})    
                ==>
                && invs_group_9(dv)
                && invs_group_10(dv)
                && invs_group_11(dv)
                && invs_group_12(dv)
                && invs_group_13(dv)
                && invs_group_14(dv)
                ;
    }  
}