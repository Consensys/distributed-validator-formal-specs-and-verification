include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"

module Att_Assumptions
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    
    // Assumption 4a
    // Let a be a new attestation duty served to an honest node n. Then
    // either a is the first served duty of n or 
    // a’s slot is greater than the slot of the latest served duty served by n.
    lemma {:axiom}  monotonic_seq_of_rcvd_att_duties<D(!new, 0)>(
        dvn: DVState,
        pubkey: BLSPubkey,        
        new_att_duty: AttestationDuty)       
    requires && is_honest_node(dvn, pubkey) 
             && var s := dvn.honest_nodes_states[pubkey];
             && f_serve_attestation_duty.requires(s, new_att_duty)
    ensures && var s := dvn.honest_nodes_states[pubkey];
            && ( || !s.latest_attestation_duty.isPresent()
                 || ( && s.latest_attestation_duty.isPresent()
                      && s.latest_attestation_duty.safe_get().slot < new_att_duty.slot 
                    )
               )

    // Assumption 4b
    // Let a be a new attestation duty served to an honest node n. 
    // For every honest node n1, for every duty d that n1 received, if d’s
    // slot is less than a’s slot, then n received d.
    lemma {:axiom}  rcvd_att_duties_as_prefixes<D(!new, 0)>(
        dvn: DVState,
        pubkey: BLSPubkey,
        s: DVCNodeState,
        new_att_duty: AttestationDuty)       
    requires && is_honest_node(dvn, pubkey) 
             && var s := dvn.honest_nodes_states[pubkey];
             && f_serve_attestation_duty.requires(s, new_att_duty)
    ensures && var s := dvn.honest_nodes_states[pubkey];
            && forall p1: BLSPubkey, duty: AttestationDuty :: 
                    && is_honest_node(dvn, p1)
                    && var s1 := dvn.honest_nodes_states[p1];
                    && duty in s1.all_rcvd_duties
                    && duty.slot < new_att_duty.slot
                        ==> duty in s.all_rcvd_duties

    // Assumption 4c
    // Let a be a new attestation duty served to an honest node n. Then
    //    - Either for every honest node n1, for every duty d that n1 received,
    //      d’s slot is less than a’s slot.
    //    - Or there exits an honest node n1 such that n1 received a.
    lemma {:axiom}  rcvd_att_duties_is_prefix_of_global_att_duties<D(!new, 0)>(
        dvn: DVState,
        pubkey: BLSPubkey,
        s: DVCNodeState,
        new_att_duty: AttestationDuty)       
    requires && is_honest_node(dvn, pubkey) 
             && var s := dvn.honest_nodes_states[pubkey];
             && f_serve_attestation_duty.requires(s, new_att_duty)
    ensures && var s := dvn.honest_nodes_states[pubkey];
            && ( || ( forall p1: BLSPubkey, duty: AttestationDuty :: 
                          && is_honest_node(dvn, p1)
                          && var s1 := dvn.honest_nodes_states[p1];                    
                          && duty in s1.all_rcvd_duties
                              ==> duty.slot < new_att_duty.slot                                                   
                    )
                  || ( exists p1: BLSPubkey :: 
                          && is_honest_node(dvn, p1)
                          && var s1 := dvn.honest_nodes_states[p1];
                          && s1.latest_attestation_duty.isPresent()
                          && new_att_duty in s1.all_rcvd_duties
                     )
               )
            
  // TODO: DVN.Init should implies this lemma.
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

  // TODO: DVN.Init should implies this lemma.
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

  
  lemma {:axiom} axiom_is_my_attestation(
    dvn: DVState,
    event: DV.Event,
    dvn': DVState
  )
  requires DV.NextEvent(dvn, event, dvn')
  requires event.HonestNodeTakingStep?
  requires event.event.ImportedNewBlock?
  ensures pred_axiom_is_my_attestation(
    dvn,
    dvn.honest_nodes_states[event.node],
    event.event.block
  )

  predicate pred_axiom_is_my_attestation(
    dvn: DVState,
    process: DVCNodeState,
    block: BeaconBlock
  )
  {
    var new_p := add_block_to_bn(process, block);
    pred_axiom_is_my_attestation_2(dvn, new_p, block)
  }

  // TODO: Modify isMyAttestation to include the entirety the forall premise 
  predicate pred_axiom_is_my_attestation_2(
    dvn: DVState,
    new_p: DVCNodeState,
    block: BeaconBlock
  )
  requires block.body.state_root in new_p.bn.state_roots_of_imported_blocks
  {
    var valIndex := bn_get_validator_index(new_p.bn, block.body.state_root, new_p.dv_pubkey);
    forall a | 
        && a in block.body.attestations 
        && isMyAttestation(
          a,
          new_p,
          block,
          valIndex
        )
      ::
      exists a' ::
        && a' in dvn.all_attestations_created
        && a'.data == a.data 
        && is_valid_attestation(a', dvn.dv_pubkey)    
  }  

}



