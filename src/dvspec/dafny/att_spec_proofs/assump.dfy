include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"

module AttAssumptions
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened AttInvariants
    
    lemma {:axiom}  monotonic_seq_of_rcvd_att_duties<D(!new, 0)>(
        dvn: DVState,
        pubkey: BLSPubkey,
        s: DVCNodeState,
        new_att_duty: AttestationDuty)       
    requires is_honest_node(dvn, pubkey) && s == dvn.honest_nodes_states[pubkey]
    requires f_serve_attestation_duty.requires(s, new_att_duty)
    ensures || !s.latest_attestation_duty.isPresent()
            || ( && s.latest_attestation_duty.isPresent()
                 && s.latest_attestation_duty.safe_get().slot < new_att_duty.slot 
               )
    
    lemma {:axiom}  rcvd_att_duties_is_prefix_of_global_att_duties<D(!new, 0)>(
        dvn: DVState,
        pubkey: BLSPubkey,
        s: DVCNodeState,
        new_att_duty: AttestationDuty)       
    requires is_honest_node(dvn, pubkey) && s == dvn.honest_nodes_states[pubkey]
    requires f_serve_attestation_duty.requires(s, new_att_duty)
    ensures || ( exists p1: BLSPubkey :: 
                    && is_honest_node(dvn, p1)
                    && var s1 := dvn.honest_nodes_states[p1];
                    && s1.latest_attestation_duty.isPresent()
                    && s1.latest_attestation_duty.safe_get() == new_att_duty
               )
            || ( forall p1: BLSPubkey :: 
                    && is_honest_node(dvn, p1)
                    && var s1 := dvn.honest_nodes_states[p1];                    
                    && ( || !s1.latest_attestation_duty.isPresent()
                         || ( && s1.latest_attestation_duty.isPresent()
                              && s1.latest_attestation_duty.safe_get().slot < new_att_duty.slot
                            )
                       )
               )
    ensures ! ( exists duty: AttestationDuty ::
                    && ! ( duty in s.all_rcvd_duties ) 
                    && duty.slot < new_att_duty.slot
                    && exists p1: BLSPubkey :: 
                            ( && is_honest_node(dvn, p1)
                              && var s1 := dvn.honest_nodes_states[p1];                     
                              && duty in s1.all_rcvd_duties
                            )
              )
    
  lemma {:axiom} constructable_signed_attestation_signature(
    dvn: DVState,
    att_shares: set<AttestationShare>) 
  ensures dvn.construct_signed_attestation_signature(att_shares).isPresent()
            <==> exists S: set<AttestationShare> ::
                    && S <= att_shares
                    && |dvn.adversary.nodes| * 2 + 1 <= |S|
                    && ( forall s1, s2: AttestationShare ::
                            && s1 in S
                            && s2 in S
                                ==> att_shares_from_same_att_data(s1, s2) )

  lemma {:axiom} agreement_on_constructed_signed_attestation_signature(
    dvn: DVState,
    att_shares1: set<AttestationShare>, 
    att_shares2: set<AttestationShare>) 
  ensures ( && dvn.construct_signed_attestation_signature(att_shares1).isPresent()
            && dvn.construct_signed_attestation_signature(att_shares2).isPresent()
            && dvn.construct_signed_attestation_signature(att_shares1).safe_get()
                  == dvn.construct_signed_attestation_signature(att_shares2).safe_get()
          )
            <==> exists S: set<AttestationShare> ::
                    && S <= att_shares1
                    && S <= att_shares2
                    && |dvn.adversary.nodes| * 2 + 1 <= |S|
                    && ( forall s1, s2: AttestationShare ::
                            && s1 in S
                            && s2 in S
                                ==> att_shares_from_same_att_data(s1, s2) )                                
}



