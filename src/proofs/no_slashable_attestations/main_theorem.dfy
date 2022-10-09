include "../../common/commons.dfy"
include "../../specs/dv/dv_attestation_creation.dfy"


include "supporting_lemmas/ind_inv.dfy"
include "supporting_lemmas/init_implies_ind_inv/init_implies_ind_inv.dfy"
include "supporting_lemmas/dv_next_preserves_ind_inv/ind_inv_dv_next.dfy"
include "supporting_lemmas/ind_inv_implies_safety/ind_inv_implies_safety.dfy"

module No_Slashable_Attestations_Main_Theorem
{
    import opened Types 
    import opened DV    
    import opened Att_Ind_Inv_With_Empty_Init_Att_Slashing_DB
    import opened Ind_Inv_DV_Init
    import opened Ind_Inv_DV_Next
    import opened Ind_Inv_Implies_Safety


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

    lemma lem_non_slashable_attestations_rec(
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
            lem_ind_inv_dv_init(trace[0]);
        }
        else 
        {
            lem_non_slashable_attestations_rec(trace, i-1);
            lem_ind_inv_dv_ind(trace[i-1], trace[i]);
        }
    }

    lemma lem_non_slashable_attestations(
        trace: iseq<DVState>
    )
    requires isValidTrace(trace)
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