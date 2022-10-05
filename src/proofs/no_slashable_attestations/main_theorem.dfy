include "../../common/commons.dfy"
include "../../specs/dvn/dvn.dfy"

include "supporting_lemmas/proofs_ind_inv.dfy"

module No_Slashable_Attestations_Main_Theorem
{
    import opened Types 
    import opened DV
    import opened Proofs_DVN_Ind_Inv


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