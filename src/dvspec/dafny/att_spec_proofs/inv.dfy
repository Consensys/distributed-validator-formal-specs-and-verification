include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"

module AttInvariants
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV

    predicate no_conflict_decisions_in_sec_3_1<D(!new, 0)>()
    {
        forall s: ConsensusInstance<D>, i1: BLSPubkey, i2: BLSPubkey | 
            && ConsensusSpec.isConditionForSafetyTrue(s)
            && i1 in s.honest_nodes_status.Keys
            && i2 in s.honest_nodes_status.Keys ::                         
                    || s.honest_nodes_status[i1] == NOT_DECIDED
                    || s.honest_nodes_status[i2] == NOT_DECIDED
                    || s.honest_nodes_status[i1] == s.honest_nodes_status[i2]
    }

    predicate no_decisions_pred_in_sec_3_1<D(!new, 0)>()
    {
        forall s: ConsensusInstance<D> ::
            ConsensusSpec.isConditionForSafetyTrue(s)
                ==> ( !s.decided_value.isPresent()
                        <==> ( forall i: BLSPubkey | i in s.honest_nodes_status.Keys ::
                                    s.honest_nodes_status[i] == NOT_DECIDED
                             )
                    ) 
    }

    predicate is_honest_node(s: DVState, n: BLSPubkey)
    {
        && n in s.all_nodes
        && !(n in s.adversary.nodes)
        && n in s.honest_nodes_states.Keys
    }

    predicate consistant_att_slashing_databases_between_honest_nodes_in_sec_3_2<D(!new, 0)>()
    {
        forall s: DVState, n1: BLSPubkey, n2: BLSPubkey |
            && is_honest_node(s, n1)
            && is_honest_node(s, n2) 
                :: || s.honest_nodes_states[n1].attestation_slashing_db <= s.honest_nodes_states[n2].attestation_slashing_db
                   || s.honest_nodes_states[n2].attestation_slashing_db <= s.honest_nodes_states[n1].attestation_slashing_db
                   
    }

    predicate consistant_attestations_in_one_slashing_db_in_sec_3_2<D(!new, 0)>()
    {
        forall s: DVState,
               pubkey: BLSPubkey, 
               nState: DVCNodeState,
               att: SlashingDBAttestation, 
               att_data: AttestationData, 
               att_duty: AttestationDuty |
            && is_honest_node(s, pubkey)
            && nState == s.honest_nodes_states[pubkey]
            && att in nState.attestation_slashing_db
            && att_duty in nState.all_rcvd_duties
            && att.signing_root == Some(hash_tree_root(att_data))
            && att_data.slot == att_duty.slot ::
                    consensus_is_valid_attestation_data(nState.attestation_slashing_db, att_data, att_duty)         
    }

    predicate curr_att_duty_is_last_served_duty_in_sec_3_3<D(!new, 0)>()        
    {
        forall dvn: DVState,
               pubkey: BLSPubkey,
               s: DVCNodeState | 
                    && is_honest_node(dvn, pubkey)
                    && s == dvn.honest_nodes_states[pubkey] :: 
                            s.current_attestation_duty.isPresent()
                                ==> ( && s.latest_attestation_duty.isPresent()
                                      && s.current_attestation_duty.safe_get() == s.latest_attestation_duty.safe_get()
                                    )
    }

    predicate exisiting_consensus_instance_for_curr_att_duty_in_sec_3_3<D(!new, 0)>()        
    {
        forall dvn: DVState,
               pubkey: BLSPubkey,
               s: DVCNodeState | 
                    && is_honest_node(dvn, pubkey)
                    && s == dvn.honest_nodes_states[pubkey] ::
                        s.current_attestation_duty.isPresent()
                                ==> ( s.current_attestation_duty.safe_get().slot 
                                        in s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys )
    }

    predicate active_consensus_instances_imples_existence_of_curr_att_duty_in_sec_3_3<D(!new, 0)>()        
    {
        forall dvn: DVState,
               pubkey: BLSPubkey,
               s: DVCNodeState | 
                    && is_honest_node(dvn, pubkey)
                    && s == dvn.honest_nodes_states[pubkey] ::
                        s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys != {}
                            ==> ( && s.current_attestation_duty.isPresent()
                                  && s.current_attestation_duty.safe_get().slot 
                                        in s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys 
                    )
    }
    
    predicate queued_duties_later_than_curr_att_duty_in_sec_3_3<D(!new, 0)>()        
    {
        forall dvn: DVState,
               pubkey: BLSPubkey,
               s: DVCNodeState | 
                    && is_honest_node(dvn, pubkey)
                    && s == dvn.honest_nodes_states[pubkey] ::
                        s.current_attestation_duty.isPresent()
                            ==> forall queued_duty: AttestationDuty |
                                    queued_duty in s.attestation_duties_queue :: 
                                        s.current_attestation_duty.safe_get().slot < queued_duty.slot
    }

    predicate submitted_att_by_curr_att_duty_in_sec_3_3<D(!new, 0)>()        
    {
        forall dvn: DVState,
               pubkey: BLSPubkey,
               s: DVCNodeState | 
                    && is_honest_node(dvn, pubkey)
                    && s == dvn.honest_nodes_states[pubkey] ::
                        s.current_attestation_duty.isPresent()
                            ==> (forall i: nat | 0 <= i && i < |s.bn.attestations_submitted| ::
                                    s.bn.attestations_submitted[i].data.slot <= s.current_attestation_duty.safe_get().slot)            
    }

    predicate none_latest_att_duty_implies_empty_att_duty_queue_in_sec_3_4<D(!new, 0)>()        
    {
        forall dvn: DVState,
               pubkey: BLSPubkey,
               s: DVCNodeState | 
                    && is_honest_node(dvn, pubkey)
                    && s == dvn.honest_nodes_states[pubkey] ::
                        !s.latest_attestation_duty.isPresent()
                            ==> |s.attestation_duties_queue| == 0
    }

    predicate queued_duties_later_than_latest_att_duty_in_sec_3_4<D(!new, 0)>()        
    {
        forall dvn: DVState,
               pubkey: BLSPubkey,
               s: DVCNodeState | 
                    && is_honest_node(dvn, pubkey)
                    && s == dvn.honest_nodes_states[pubkey] ::
                        s.latest_attestation_duty.isPresent()
                            ==> forall queued_duty: AttestationDuty |
                                    queued_duty in s.attestation_duties_queue :: 
                                        s.latest_attestation_duty.safe_get().slot < queued_duty.slot
    }

    predicate submitted_att_by_latest_att_duty_in_sec_3_4<D(!new, 0)>()        
    {
        forall dvn: DVState,
               pubkey: BLSPubkey,
               s: DVCNodeState | 
                    && is_honest_node(dvn, pubkey)
                    && s == dvn.honest_nodes_states[pubkey] ::
                        s.latest_attestation_duty.isPresent()
                            ==> (forall i: nat | 0 <= i && i < |s.bn.attestations_submitted| ::
                                    s.bn.attestations_submitted[i].data.slot <= s.latest_attestation_duty.safe_get().slot)            
    }

    predicate active_consensus_instances_for_slots_until_latest_att_duty_in_sec_3_4<D(!new, 0)>()        
    {
        forall dvn: DVState,
               pubkey: BLSPubkey,
               s: DVCNodeState | 
                    && is_honest_node(dvn, pubkey)
                    && s == dvn.honest_nodes_states[pubkey] ::
                        s.latest_attestation_duty.isPresent()
                            ==> ( forall i: Slot | i in s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys ::
                                        i <= s.latest_attestation_duty.safe_get().slot )
    }

    predicate no_active_consensus_instances_for_queued_att_duties_in_sec_3_5<D(!new, 0)>()        
    {
        forall dvn: DVState,
               pubkey: BLSPubkey,
               s: DVCNodeState,
               i: Slot, 
               j: nat | 
                    && is_honest_node(dvn, pubkey)
                    && s == dvn.honest_nodes_states[pubkey] 
                    && i in s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys 
                    && 0 <= j
                    && j < |s.attestation_duties_queue| ::
                        i <= s.attestation_duties_queue[j].slot
    }

    predicate at_most_one_active_consensus_instances_has_not_decided_in_sec_3_5<D(!new, 0)>()        
    {
        forall dvn: DVState,
               pubkey: BLSPubkey,
               s: DVCNodeState,
               i: Slot, 
               j: Slot   | 
                    && is_honest_node(dvn, pubkey)
                    && s == dvn.honest_nodes_states[pubkey] 
                    && i in s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys 
                    && 0 <= j
                    && j < |s.attestation_duties_queue| ::
                        i <= s.attestation_duties_queue[j].slot
    }

    predicate att_from_imported_block_is_decided_value_in_sec_3_6<D(!new, 0)>()        
    {
        forall dvn: DVState,
               pubkey: BLSPubkey,
               s: DVCNodeState,
               i: nat,
               slot: Slot  | 
                    && is_honest_node(dvn, pubkey)
                    && s == dvn.honest_nodes_states[pubkey] 
                    && i in s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys 
                    && 0 <= i
                    && i < |s.bn.attestations_submitted|
                    && slot == s.bn.attestations_submitted[i].data.slot ::
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && s.bn.attestations_submitted[i].data == dvn.consensus_on_attestation_data[slot].decided_value.safe_get()
    }

    predicate AttConsensusDecided_is_decided_value_in_sec_3_7<D(!new, 0)>()        
    {
        forall dvn: DVState,
               pubkey: BLSPubkey,
               s: DVCNodeState,
               s': DVCNodeState,               
               slot: Slot,
               att_data: AttestationData  | 
                    && is_honest_node(dvn, pubkey)
                    && s == dvn.honest_nodes_states[pubkey] 
                    && f_att_consensus_decided.requires(s, slot, att_data)
                    && s' == f_att_consensus_decided(s, slot, att_data).state ::
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && dvn.consensus_on_attestation_data[slot].decided_value.safe_get() == att_data                        
    }

    predicate strictly_monotonic_att_duties_queue_in_sec_3_7<D(!new, 0)>()        
    {
        forall dvn: DVState,
               pubkey: BLSPubkey,
               s: DVCNodeState,               
               i1: nat,
               i2: nat | 
                    && is_honest_node(dvn, pubkey)
                    && s == dvn.honest_nodes_states[pubkey] 
                    && 0 <= i1
                    && i1 < |s.attestation_duties_queue|
                    && 0 <= i2
                    && i2 < |s.attestation_duties_queue| ::
                        i1 < i2 ==> s.attestation_duties_queue[i1] < s.attestation_duties_queue[i2]
    }

    predicate existing_share_from_node(
        att_shares: set<AttestationShare>, 
        att_data: AttestationData, 
        s: DVCNodeState,
        slot: Slot
    )
    {
        exists share: AttestationShare,                                   
               root: Root,
               fork_version: Version,
               epoch: Epoch,
               start_slot: Slot,
               att_sig: BLSSignature ::
                    && start_slot == compute_start_slot_at_epoch(epoch) 
                    && fork_version == bn_get_fork_version(slot)
                    && root == compute_attestation_signing_root(att_data, fork_version)
                    && att_sig == rs_sign_attestation(att_data, fork_version, root, s.rs)
                    && share in att_shares
                    && share.data == att_data
                    && share.signature == att_sig
                    && fork_version == bn_get_fork_version(att_data.slot)                                                                                
    }

    predicate constructable_set_of_att_shares_has_at_least_one_share_from_honest_node_in_sec_3_7<D(!new, 0)>()        
    {
        forall dvn: DVState,
               pubkey: BLSPubkey,
               s: DVCNodeState,               
               slot: Slot,
               att_data: AttestationData,
               att_shares: set<AttestationShare>,
               aggregation_bits: seq<bool> | 
                    && is_honest_node(dvn, pubkey)
                    && s == dvn.honest_nodes_states[pubkey]
                    && slot in s.rcvd_attestation_shares.Keys
                    && (att_data, aggregation_bits) in s.rcvd_attestation_shares[slot].Keys
                    && att_data.slot == slot
                    && att_shares == s.rcvd_attestation_shares[slot][(att_data, aggregation_bits)]
                    && s.construct_signed_attestation_signature(att_shares).isPresent()
                    && ( forall share: AttestationShare | share in att_shares :: share.data == att_data ) ::
                            exists pubkey1: BLSPubkey,
                            s1: DVCNodeState ::
                                    && is_honest_node(dvn, pubkey1)
                                    && s1 == dvn.honest_nodes_states[pubkey1]
                                    && existing_share_from_node(att_shares, att_data, s1, slot)                                   
    }

    predicate no_missing_att_in_db_cond1_in_sec_3_7<D(!new, 0)>()        
    {
        forall dvn: DVState,
               pubkey: BLSPubkey,
               s: DVCNodeState :: 
                    && is_honest_node(dvn, pubkey)
                    && s == dvn.honest_nodes_states[pubkey]
                    && !s.current_attestation_duty.isPresent()
                    && s.latest_attestation_duty.isPresent() 
                        ==> forall slot: Slot,
                                   att_data: AttestationData,
                                   bits: seq<bool>,                                   
                                   att_shares: set<AttestationShare> ::
                                        && slot <= s.latest_attestation_duty.safe_get().slot
                                        && slot in s.rcvd_attestation_shares.Keys
                                        && (att_data, bits) in s.rcvd_attestation_shares[slot].Keys
                                        && att_data.slot == slot
                                        && att_shares == s.rcvd_attestation_shares[slot][(att_data, bits)]
                                        && s.construct_signed_attestation_signature(att_shares).isPresent() 
                                        && (forall share: AttestationShare ::
                                                share in att_shares ==> share.data == att_data )
                                                ==> exists slashingdbAtt: SlashingDBAttestation ::
                                                        && slashingdbAtt in s.attestation_slashing_db            
                                                        && Some(hash_tree_root(att_data)) == slashingdbAtt.signing_root                                                                 
    }

    predicate no_missing_att_in_db_cond2_in_sec_3_7<D(!new, 0)>()        
    {
        forall dvn: DVState,
               pubkey: BLSPubkey,
               s: DVCNodeState :: 
                    && is_honest_node(dvn, pubkey)
                    && s == dvn.honest_nodes_states[pubkey]
                    && s.current_attestation_duty.isPresent()
                    && s.latest_attestation_duty.isPresent() 
                        ==> forall slot: Slot,
                                   att_data: AttestationData,
                                   bits: seq<bool>,                                   
                                   att_shares: set<AttestationShare> ::
                                        && slot < s.current_attestation_duty.safe_get().slot
                                        && slot in s.rcvd_attestation_shares.Keys
                                        && (att_data, bits) in s.rcvd_attestation_shares[slot].Keys
                                        && att_data.slot == slot
                                        && att_shares == s.rcvd_attestation_shares[slot][(att_data, bits)]
                                        && s.construct_signed_attestation_signature(att_shares).isPresent() 
                                        && (forall share: AttestationShare ::
                                                share in att_shares ==> share.data == att_data )
                                                ==> exists slashingdbAtt: SlashingDBAttestation ::
                                                        && slashingdbAtt in s.attestation_slashing_db            
                                                        && Some(hash_tree_root(att_data)) == slashingdbAtt.signing_root                                                                 
    }

    predicate pred24()
    {
        forall 
            dvn: DVState, 
            i: Slot, 
            pred: AttestationData -> bool ::
                pred in dvn.consensus_on_attestation_data[i].honest_nodes_validity_functions
                    ==> ( forall att_data: AttestationData ::
                            pred(att_data) 
                                ==> ( exists 
                                        att_duty: AttestationDuty,
                                        pubkey: BLSPubkey, 
                                        db: set<SlashingDBAttestation>,
                                        s: DVCNodeState ::
                                            && is_honest_node(dvn, pubkey)
                                            && s == dvn.honest_nodes_states[pubkey]
                                            && consensus_is_valid_attestation_data(db, att_data, att_duty) 
                                            && att_duty.slot == i
                                            && db <= dvn.honest_nodes_states[pubkey].attestation_slashing_db
                                    )
                        ) 
    }    

    predicate sent_att_share_from_honest_node_in_sec_3_7<D(!new, 0)>()        
    {
        forall dvn: DVState, att_share: AttestationShare :: 
            && att_share in dvn.att_network.allMessagesSent
            && ( exists pubkey: BLSPubkey, 
                      s: DVCNodeState,
                      root: Root,
                      fork_version: Version :: 
                            && is_honest_node(dvn, pubkey)
                            && s == dvn.honest_nodes_states[pubkey]
                            && fork_version == bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch))
                            && root == compute_attestation_signing_root(att_share.data, fork_version)
                            && att_share.signature == 
                               rs_sign_attestation(att_share.data, 
                                                  fork_version, 
                                                  root, 
                                                  s.rs)
               )
                    ==> ( && dvn.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent()
                          && att_share.data == dvn.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get()
                        )
               
    }

    predicate fixed_set_all_nodes_in_sec_3_7<D(!new, 0)>(
        s: DVCNodeState, 
        e: Types.Event,
        s': DVCNodeState)
    requires f_process_event.requires(s, e)
    {
        s' == DVCNode_Spec.f_process_event(s, e).state ==> s.peers == s'.peers                
    }
}