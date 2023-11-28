include "../../common/commons.dfy"
include "../../specs/dv/dv_attestation_creation.dfy"

include "supporting_lemmas/ind_inv.dfy"
include "supporting_lemmas/init_implies_ind_inv/init_implies_ind_inv.dfy"
include "supporting_lemmas/dv_next_preserves_ind_inv/ind_inv_dv_next.dfy"
include "supporting_lemmas/ind_inv_implies_safety/ind_inv_implies_safety.dfy"

include "../bn_axioms.dfy"
include "../rs_axioms.dfy"
include "./supporting_lemmas/ind_inv_implies_safety/core_proofs.dfy"

module No_Slashable_Attestations_Main_Theorem
{
    import opened Types
    import opened Att_DV
    import opened Att_Ind_Inv_With_Empty_Init_Att_Slashing_DB
    import opened Ind_Inv_Att_DV_Init
    import opened Ind_Inv_Att_DV_Next
    import opened Ind_Inv_Implies_Safety
    import opened Signing_Methods
    import opened BN_Axioms
    import opened RS_Axioms
    import opened Core_Proofs

    predicate valid_trace(
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
    requires valid_trace(trace)
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
    requires valid_trace(trace)
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

    lemma adversarSpecCounterEx(s: AttDVState,s':AttDVState, e:DVAttestationEvent,a:Attestation,trace:iseq<AttDVState>)
    requires valid_trace(trace)
    requires exists i :: i in trace && trace[i] == s && trace[i+1] == s'
    requires Att_DV.next_preconditions(s)
    requires Att_DV.next(s,s')
    requires Att_DV.next_event_preconditions(s, e)  
    requires Att_DV.next_event(s, e, s')
    requires e.AdversaryTakingStep? 
    requires Att_DV.next_adversary(s,e.node,e.new_attestation_shares_sent,e.messagesReceivedByTheNode,s');
    requires |s.all_attestations_created| > 1;
    requires forall a | a in s.all_attestations_created :: Att_DV.att_signature_is_signed_with_pubkey(a,s.dv_pubkey);
    requires non_slashable_attestations(s);
    requires a in s.all_attestations_created;
    requires
            && var sa := a.data.slot+1;
            && var adata' := AttestationData(sa,a.data.index,a.data.beacon_block_root,a.data.source,a.data.target);
            && var fork_version := af_bn_get_fork_version(compute_start_slot_at_epoch(adata'.target.epoch));
            && var attestation_signing_root := compute_attestation_signing_root(adata', fork_version);
            && var rs := RSState(s'.dv_pubkey);
            && var a' := Attestation(a.aggregation_bits,adata',af_rs_sign_attestation(adata', fork_version,
                            attestation_signing_root, rs));
            && (&& a' in s'.all_attestations_created)
    ensures && var sa := a.data.slot+1;
            && var adata' :=
                    AttestationData(sa,a.data.index,a.data.beacon_block_root,a.data.source,a.data.target);
            && var fork_version :=
                    af_bn_get_fork_version(compute_start_slot_at_epoch(adata'.target.epoch));
            && var attestation_signing_root := 
                    compute_attestation_signing_root(adata', fork_version);
            && var rs := RSState(s'.dv_pubkey);
            && var a' :=
                    Attestation(a.aggregation_bits,adata', af_rs_sign_attestation(adata', fork_version,
                    attestation_signing_root, rs));
            && (&& a in s'.all_attestations_created
                && a' in s'.all_attestations_created
                && att_signature_is_signed_with_pubkey(a',s'.dv_pubkey)
                && att_signature_is_signed_with_pubkey(a,s'.dv_pubkey)
                && is_slashable_attestation_data_eth_spec(a.data,a'.data)
                && !non_slashable_attestations(s'));
    {
        // rs_attestation_sign_and_verification_propetries<AttestationData>();
    }


}