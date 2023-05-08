include "../../../../common/commons.dfy"
include "../../common/attestation_creation_instrumented.dfy"
include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_attestation_creation.dfy"
include "../../../../specs/dvc/dvc_attestation_creation.dfy"

include "../../../common/helper_sets_lemmas.dfy"
include "../../../no_slashable_attestations/common/common_proofs.dfy"
include "../../../no_slashable_attestations/common/att_dvc_spec_axioms.dfy"

include "../dv_next_preserves_ind_inv/proofs_intermediate_steps.dfy"
include "../dv_next_preserves_ind_inv/ind_inv_dv_next.dfy"

include "../inv.dfy"
include "../ind_inv.dfy"

include "core_proofs.dfy"


module Ind_Inv_Implies_Safety
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened Att_DVC_Spec
    import opened Att_DV
    import opened Att_Ind_Inv_With_Empty_Init_Att_Slashing_DB
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    
    import opened Core_Proofs
    import opened Ind_Inv_Att_DV_Next
    import opened Proofs_Intermediate_Steps 

    predicate non_slashable_attestations(
        dv: Att_DVState
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

    lemma lem_ind_inv_no_slashable_submitted_attestations(dv: Att_DVState)
    requires ind_inv(dv)    
    ensures non_slashable_attestations(dv)
    {   
        lem_ind_inv_implies_intermediate_steps(dv);

        forall a: Attestation, a': Attestation
                    | 
                    && a in dv.all_attestations_created
                    && is_valid_attestation(a, dv.dv_pubkey)
                    && a' in dv.all_attestations_created
                    && is_valid_attestation(a', dv.dv_pubkey)     
        ensures && !is_slashable_attestation_data_eth_spec(a.data, a'.data)
                && !is_slashable_attestation_data_eth_spec(a'.data, a.data);
        {
            lem_no_slashable_submitted_attestations(dv, a, a');
        }
    }

}