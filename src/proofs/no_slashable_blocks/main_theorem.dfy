include "../../common/commons.dfy"
include "../../specs/dv/dv_block_proposer.dfy"


include "supporting_lemmas/ind_inv.dfy"
include "supporting_lemmas/init_implies_ind_inv/init_implies_ind_inv.dfy"
include "supporting_lemmas/dv_next_preserves_ind_inv/ind_inv_dv_next.dfy"
include "supporting_lemmas/ind_inv_implies_safety/ind_inv_implies_safety.dfy"

module No_Slashable_Blocks_Main_Theorem
{
    import opened Types
    import opened Block_DV    
    import opened Block_Ind_Inv_With_Empty_Initial_Block_Slashing_DB
    import opened Ind_Inv_DV_Init
    import opened Ind_Inv_DV_Next
    import opened Ind_Inv_Implies_Safety


    predicate valid_trace(
        trace: iseq<BlockDVState>
    )  
    {
        && Block_DV.init(trace[0], {})
        && (
            forall i: Slot ::
                Block_DV.next_preconditions(trace[i]) ==> Block_DV.next(trace[i], trace[i+1])
        )
    }  

    lemma lem_non_slashable_submitted_data_rec(
        trace: iseq<BlockDVState>,
        i: Slot
    )
    requires valid_trace(trace)
    ensures forall j | 0 <= j <= i ::
                && next_preconditions(trace[j])  
                && ind_inv(trace[j])
    {
        forall j | 0 <= j <= i 
        ensures && next_preconditions(trace[j])  
                && ind_inv(trace[j])
        {
            if i == 0 
            {
                lem_ind_inv_dv_init(trace[0]);
            }
            else 
            {
                lem_non_slashable_submitted_data_rec(trace, i-1);
                lem_ind_inv_dv_ind_inv_next_preconditions(trace[i-1], trace[i]);
            }
        }
    }

    lemma lem_non_slashable_submitted_data(
        trace: iseq<BlockDVState>
    )
    requires valid_trace(trace)
    ensures forall i:nat :: non_slashable_submitted_data(trace[i])
    {
        forall i:nat
        ensures ind_inv(trace[i])
        ensures non_slashable_submitted_data(trace[i])
        {
            lem_non_slashable_submitted_data_rec(trace, i);
            lem_ind_inv_no_slashable_submitted_data(trace[i]);
        }
        
    }    
}