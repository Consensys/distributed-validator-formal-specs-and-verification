include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"
include "../att_spec_proofs/core_proofs.dfy"
include "../att_spec_proofs/ci_ind_inv.dfy"
include "../att_spec_proofs/dvc_ind_inv.dfy"
include "../att_spec_proofs/dvn_ind_inv.dfy"

module Proof_Test
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Att_Ind_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Helper_Sets_Lemmas

/*
    lemma inv53(dvn: DVState, s: Slot)
    ensures && var ci := dvn.consensus_on_attestation_data[s];
            // && quorum(|ci.all_nodes|) <= |ci.honest_nodes_status|
            && dvn.all_nodes == ci.all_nodes
            && dvn.honest_nodes_states.Keys == ci.honest_nodes_status.Keys
    {}
*/

    lemma lemma_4_1_a_i(dvn: DVState, a: Attestation, a': Attestation, hn: BLSPubkey, hn': BLSPubkey)
    requires |dvn.all_nodes| > 0
    requires inv52(dvn)
    requires pred_4_1_b(dvn)
    requires pred_4_1_c(dvn)
    requires pred_4_1_f_a(dvn)
    requires inv42(dvn)   
    requires hn in dvn.honest_nodes_states.Keys 
    requires hn' in dvn.honest_nodes_states.Keys
    requires a in dvn.honest_nodes_states[hn].bn.attestations_submitted
    requires a' in dvn.honest_nodes_states[hn'].bn.attestations_submitted    
    {
        
        var hna, att_share :|
                && is_honest_node(dvn, hna)
                && att_share in dvn.att_network.allMessagesSent
                && att_share.data == a.data
                && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));
                && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
                && verify_bls_siganture(attestation_signing_root, att_share.signature, hna);     

        var hna', att_share' :|
                && is_honest_node(dvn, hna)
                && att_share' in dvn.att_network.allMessagesSent
                && att_share'.data == a'.data
                && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share'.data.target.epoch));
                && var attestation_signing_root := compute_attestation_signing_root(att_share'.data, fork_version);
                && verify_bls_siganture(attestation_signing_root, att_share'.signature, hna');  
                

        assert
                && dvn.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent()
                && dvn.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data;       

        assert
                && dvn.consensus_on_attestation_data[att_share'.data.slot].decided_value.isPresent()
                && dvn.consensus_on_attestation_data[att_share'.data.slot].decided_value.safe_get() == att_share'.data;   

        var consa := dvn.consensus_on_attestation_data[a.data.slot];
        var consa' := dvn.consensus_on_attestation_data[a'.data.slot];                    

        assert is_a_valid_decided_value(consa); 
        assert is_a_valid_decided_value(consa');  

        assert consa.decided_value.isPresent();

        var h_nodes_a :| is_a_valid_decided_value_according_to_set_of_nodes(consa, h_nodes_a);
        var h_nodes_a' :| is_a_valid_decided_value_according_to_set_of_nodes(consa', h_nodes_a');

        assert consa.all_nodes == consa'.all_nodes == dvn.all_nodes;
    }
}