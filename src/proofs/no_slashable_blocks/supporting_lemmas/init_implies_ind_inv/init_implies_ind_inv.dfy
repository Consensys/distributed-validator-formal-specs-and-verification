include "../../../../common/block_proposer/block_types.dfy"
include "../../../../common/block_proposer/block_common_functions.dfy"
include "../../../../common/block_proposer/block_signing_functions.dfy"
include "../../common/dvc_block_proposer_instrumented.dfy"

include "../../../../specs/consensus/block_consensus.dfy"
include "../../../../specs/network/block_network.dfy"
include "../../../../specs/dv/dv_block_proposer.dfy"

include "../inv.dfy"
include "../ind_inv.dfy"

module Ind_Inv_DV_Init
{
    import opened Block_Types
    import opened Block_Signing_Functions
    import opened Block_Common_Functions
    import opened Block_Consensus_Spec
    import opened Block_Network_Spec
    import opened DVC_Block_Proposer_Spec_Instr
    import opened DV_Block_Proposer_Spec 
    import opened Block_Inv_With_Empty_Initial_Block_Slashing_DB
    import opened Block_Ind_Inv_With_Empty_Initial_Block_Slashing_DB
    
    lemma lem_ind_inv_dv_init(dv: DVState)       
    requires DV_Block_Proposer_Spec.Init(dv, {})    
    ensures ind_inv(dv)
    ensures NextPreCond(dv)
    {
        assert  DV_Block_Proposer_Spec.Init(dv, {})  
                ==>                 
                && invs_group_1(dv)
                && invs_group_2(dv)
        ;
        assert  DV_Block_Proposer_Spec.Init(dv, {})  
                ==>                 
                && invs_group_3(dv)                         
                && invs_group_4(dv)
                && invs_group_5(dv)   
                && invs_group_6(dv)                     
        ;

        assert  DV_Block_Proposer_Spec.Init(dv, {})    
                ==>
                && invs_group_7(dv)
                && invs_group_8(dv)           
                && invs_group_9(dv)
                && invs_group_10(dv)
                && invs_group_11(dv)
                && invs_group_12(dv)
                && invs_group_13(dv)
                && invs_group_14(dv)
                && invs_group_15(dv)
        ;
    }  
}