include "../../common/commons.dfy"
include "../../specs/dv/dv_attestation_creation.dfy"


include "supporting_lemmas/ind_inv.dfy"
include "supporting_lemmas/init_implies_ind_inv/init_implies_ind_inv.dfy"
include "supporting_lemmas/dv_next_preserves_ind_inv/ind_inv_dv_next.dfy"
include "supporting_lemmas/ind_inv_implies_safety/ind_inv_implies_safety.dfy"

module No_Slashable_Attestations_Main_Theorem
{
    import opened Types 
    import opened Att_DV    
    import opened Att_Ind_Inv_With_Empty_Init_Att_Slashing_DB
    import opened Ind_Inv_Att_DV_Init
    import opened Ind_Inv_Att_DV_Next
    import opened Ind_Inv_Implies_Safety


    predicate is_valid_trace(
        trace: iseq<AttDVState>
    )  
    {
        && Att_DV.init(trace[0], {})
        && (
            forall i: Slot ::
                Att_DV.next_preconditions(trace[i]) ==> Att_DV.next(trace[i], trace[i+1])
        )
    }  

    lemma lem_non_slashable_attestations_rec(
        trace: iseq<AttDVState>,
        i: Slot
    )
    requires is_valid_trace(trace)
    ensures forall j | 0 <= j <= i ::
        && next_preconditions(trace[j])  
        && ind_inv(trace[j])
    {
        if i == 0 
        {
            lem_ind_inv_dv_init(trace[0]);
        }
        else 
        {
            lem_non_slashable_attestations_rec(trace, i-1);
            lem_ind_inv_dv_ind_inv_next_preconditions(trace[i-1], trace[i]);
        }
    }

    lemma lem_non_slashable_attestations(
        trace: iseq<AttDVState>
    )
    requires is_valid_trace(trace)
    ensures forall i:nat :: non_slashable_attestations(trace[i])
    {
        forall i:nat
        ensures ind_inv(trace[i])
        ensures non_slashable_attestations(trace[i])
        {
            lem_non_slashable_attestations_rec(trace, i);
            lem_ind_inv_no_slashable_submitted_attestations(trace[i]);
        }
        
    }    
}