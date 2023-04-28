include "../../../../common/commons.dfy"

include "../../common/dvc_block_proposer_instrumented.dfy"

include "../../../../specs/consensus/block_consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_block_proposer.dfy"

include "../inv.dfy"
include "../ind_inv.dfy"


module Ind_Inv_Implies_Safety
{
    import opened Types
    
    import opened CommonFunctions
    import opened Block_Consensus_Spec
    import opened NetworkSpec
    import opened DVC_Block_Proposer_Spec_Instr
    import opened DV_Block_Proposer_Spec 
    import opened Block_Inv_With_Empty_Initial_Block_Slashing_DB
    import opened Block_Ind_Inv_With_Empty_Initial_Block_Slashing_DB

    predicate non_slashable_submitted_blocks(
        dv: DVState
    )
    {
        && inv_at_most_one_submitted_signed_beacon_block_with_an_available_signing_root_for_every_slot(dv)
    }

    lemma lem_ind_inv_no_slashable_submitted_blocks(dv: DVState)
    requires ind_inv(dv)    
    ensures non_slashable_submitted_blocks(dv)
    { }

}