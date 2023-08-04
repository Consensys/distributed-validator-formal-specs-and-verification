include "../../../../common/commons.dfy"
include "../../common/dvc_attestation_creation_instrumented.dfy"
include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_attestation_creation.dfy"
include "../inv.dfy"
include "../ind_inv.dfy"

module Ind_Inv_Att_DV_Init
{
    import opened Types 
    import opened Common_Functions
    import opened Set_Seq_Helper
    import opened Signing_Methods
    import opened Consensus
    import opened Consensus_Engine
    import opened Network_Spec
    import opened Att_DVC
    import opened Att_DV
    import opened Att_Ind_Inv_With_Empty_Init_Att_Slashing_DB
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    
    lemma lem_ind_inv_dv_init(dv: AttDVState)       
    requires Att_DV.init(dv, {})    
    ensures ind_inv(dv)
    ensures next_preconditions(dv)
    {
        assert  && invs_group_1(dv)
                && invs_group_2(dv)
        ;
        assert  && invs_group_3(dv)                         
                && invs_group_4(dv)
                && invs_group_5(dv)   
                && invs_group_6(dv)                     
        ;

        assert forall s: Slot ::
        Consensus.init(dv.consensus_on_attestation_data[s], dv.all_nodes, dv.honest_nodes_states.Keys);

        assert  && invs_group_7(dv)
                && invs_group_8(dv)           
                && invs_group_9(dv)
                && invs_group_10(dv)
                && invs_group_11(dv)
                && invs_group_12(dv)
                && invs_group_13(dv)
                && invs_group_14(dv)
        ;
    }  
}