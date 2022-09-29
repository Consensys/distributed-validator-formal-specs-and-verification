include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"
include "../att_spec_proofs/fnc_invs_1_26.dfy"
include "../att_spec_proofs/helper_sets_lemmas.dfy"
include "../att_spec_proofs/dvn_next_invs_1_7.dfy"
include "../att_spec_proofs/dvn_next_invs_8_18.dfy"
include "../att_spec_proofs/dvn_next_invs_19_26.dfy"
include "../att_spec_proofs/common_proofs.dfy"
include "../att_spec_proofs/fnc_invs_27.dfy"

module Incomplete_Proofs 
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB    
    import opened Helper_Sets_Lemmas
    import opened DVN_Next_Invs_1_7
    import opened DVN_Next_Invs_8_18
    import opened DVN_Next_Invs_19_26
    import opened Fnc_Invs_1_26    
    import opened Fnc_Invs_27
    import opened Common_Proofs
    

    lemma {:axiom} axiom_inv37(
        dvn: DVState
    )    
    ensures inv37(dvn)    


    lemma lemma_inv38_inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(
        dvn: DVState
    )
    requires inv38(dvn)
    ensures inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(dvn)
    {}

    predicate inv_attestation_consensus_active_instances_predicate_is_in_att_slashing_db_hist_body
    (
        n_state: DVCNodeState,
        cid: Slot
    )
    {
        && cid in n_state.attestation_consensus_engine_state.attestation_consensus_active_instances 
        ==>
        (
            && cid in n_state.attestation_consensus_engine_state.att_slashing_db_hist
            && n_state.attestation_consensus_engine_state.attestation_consensus_active_instances[cid].validityPredicate in n_state.attestation_consensus_engine_state.att_slashing_db_hist[cid] 
        )
    }

    predicate inv_attestation_consensus_active_instances_predicate_is_in_att_slashing_db_hist(dvn: DVState)    
    {
        forall hn, cid |
            && hn in dvn.honest_nodes_states.Keys        
            ::
            inv_attestation_consensus_active_instances_predicate_is_in_att_slashing_db_hist_body(dvn.honest_nodes_states[hn], cid)
             
    }      

    lemma lemma_inv29_inv_attestation_consensus_active_instances_predicate_is_in_att_slashing_db_hist(dvn: DVState)    
    requires inv29(dvn)
    ensures inv_attestation_consensus_active_instances_predicate_is_in_att_slashing_db_hist(dvn)
    {}    
}