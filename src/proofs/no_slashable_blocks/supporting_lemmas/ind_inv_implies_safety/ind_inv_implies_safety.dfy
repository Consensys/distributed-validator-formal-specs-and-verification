include "../../../../common/block_proposer/block_types.dfy"
include "../../../../common/block_proposer/block_common_functions.dfy"
include "../../../../common/block_proposer/block_signing_functions.dfy"
include "../../common/dvc_block_proposer_instrumented.dfy"

include "../../../../specs/consensus/block_consensus.dfy"
include "../../../../specs/network/block_network.dfy"
include "../../../../specs/dv/dv_block_proposer.dfy"

include "../inv.dfy"
include "../ind_inv.dfy"
// include "../dv_next_preserves_ind_inv/proofs_intermediate_steps.dfy"


module Ind_Inv_Implies_Safety
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
    // import opened Proofs_Intermediate_Steps

    predicate non_slashable_submitted_blocks(
        dv: DVState
    )
    {
        && inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty(dv)
        && inv_at_most_submitted_signed_beacon_block_for_every_slot(dv)
    }

    lemma lem_ind_inv_no_slashable_submitted_blocks(dv: DVState)
    requires ind_inv(dv)    
    ensures non_slashable_submitted_blocks(dv)
    {   
        // lem_ind_inv_implies_intermediate_steps(dv);
    }

}