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

    predicate no_conflict_decisions_pred1_in_sec_3_1<D(!new, 0)>(s: ConsensusInstance<D>)
    {
        forall i1: BLSPubkey, i2: BLSPubkey | 
            && ConsensusSpec.isConditionForSafetyTrue(s)
            && i1 in s.honest_nodes_status.Keys
            && i2 in s.honest_nodes_status.Keys ::                         
                    || s.honest_nodes_status[i1] == NOT_DECIDED
                    || s.honest_nodes_status[i2] == NOT_DECIDED
                    || s.honest_nodes_status[i1] == s.honest_nodes_status[i2]
    }

    predicate no_decisions_pred2_in_sec_3_1<D(!new, 0)>(s: ConsensusInstance<D>)
    {
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

    predicate consistant_att_slashing_databases_between_honest_nodes_pred3_in_sec_3_2<D(!new, 0)>(s: DVState)
    {
        forall n1: BLSPubkey, n2: BLSPubkey |
            && is_honest_node(s, n1)
            && is_honest_node(s, n2) 
                :: || s.honest_nodes_states[n1].attestation_slashing_db <= s.honest_nodes_states[n2].attestation_slashing_db
                   || s.honest_nodes_states[n2].attestation_slashing_db <= s.honest_nodes_states[n1].attestation_slashing_db
                   
    }

    predicate consistant_attestations_in_one_slashing_db_pred4_in_sec_3_2<D(!new, 0)>(dvn: DVState)
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var nState := dvn.honest_nodes_states[pubkey];
            && var db := nState.attestation_slashing_db;
            && forall att: SlashingDBAttestation | att in db ::
                    exists att_data: AttestationData, 
                           att_duty: AttestationDuty ::
                                && att_duty in nState.all_rcvd_duties
                                && att.signing_root == Some(hash_tree_root(att_data))            
                                && att_data.slot == att_duty.slot 
                                && consensus_is_valid_attestation_data(db, att_data, att_duty)         
    }

    predicate curr_att_duty_is_last_served_duty_pred5_in_sec_3_3<D(!new, 0)>(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && s.current_attestation_duty.isPresent()
                    ==> ( && s.latest_attestation_duty.isPresent()
                          && s.current_attestation_duty.safe_get() == s.latest_attestation_duty.safe_get()
                        )
    }

    predicate exisiting_consensus_instance_for_curr_att_duty_pred6_in_sec_3_3<D(!new, 0)>(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && s.current_attestation_duty.isPresent()
                    ==> s.current_attestation_duty.safe_get().slot 
                            in s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys 
    }

    predicate active_consensus_instances_imples_existence_of_curr_att_duty_pred7_in_sec_3_3<D(!new, 0)>(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys != {}
                    ==> ( && s.current_attestation_duty.isPresent()
                          && s.current_attestation_duty.safe_get().slot 
                                in s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys 
                        )
    }
    
    predicate queued_duties_later_than_curr_att_duty_pred8_in_sec_3_3<D(!new, 0)>(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && s.current_attestation_duty.isPresent()
                    ==> forall queued_duty: AttestationDuty | queued_duty in s.attestation_duties_queue :: 
                            s.current_attestation_duty.safe_get().slot < queued_duty.slot
    }

    predicate submitted_att_by_curr_att_duty_pred9_in_sec_3_3<D(!new, 0)>(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && s.current_attestation_duty.isPresent()
                    ==> forall i: nat | 0 <= i && i < |s.bn.attestations_submitted| ::
                            s.bn.attestations_submitted[i].data.slot <= s.current_attestation_duty.safe_get().slot
    }

    predicate none_latest_att_duty_implies_empty_att_duty_queue_pred10_in_sec_3_4<D(!new, 0)>(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && !s.latest_attestation_duty.isPresent()
                    ==> |s.attestation_duties_queue| == 0
    }

    predicate queued_duties_later_than_latest_att_duty_pred11_in_sec_3_4<D(!new, 0)>(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && s.latest_attestation_duty.isPresent()
                    ==> forall queued_duty: AttestationDuty | queued_duty in s.attestation_duties_queue :: 
                            s.latest_attestation_duty.safe_get().slot < queued_duty.slot
    }

    predicate submitted_att_by_latest_att_duty_pred12_in_sec_3_4<D(!new, 0)>(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && s.latest_attestation_duty.isPresent()
                    ==> forall i: nat | 0 <= i && i < |s.bn.attestations_submitted| ::
                            s.bn.attestations_submitted[i].data.slot <= s.latest_attestation_duty.safe_get().slot
    }

    predicate active_consensus_instances_for_slots_until_latest_att_duty_pred13_in_sec_3_4<D(!new, 0)>(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && s.latest_attestation_duty.isPresent()
                    ==> forall i: Slot | i in s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys ::
                            i <= s.latest_attestation_duty.safe_get().slot
    }

    predicate no_active_consensus_instances_for_queued_att_duties_pred14_in_sec_3_5<D(!new, 0)>(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && forall i: Slot, j: nat | 
                    && i in s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys 
                    && 0 <= j
                    && j < |s.attestation_duties_queue| ::
                        i < s.attestation_duties_queue[j].slot
    }

    /*
    // Seems wrong
    predicate at_most_one_active_consensus_instances_has_not_decided_pred15_in_sec_3_5<D(!new, 0)>(dvn: DVState)        
    {
        forall pubkey: BLSPubkey,
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
    */

    predicate att_from_imported_block_is_decided_value_pred16_in_sec_3_6<D(!new, 0)>(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && forall i: nat |                     
                    // && i in s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys 
                    && 0 <= i
                    && i < |s.bn.attestations_submitted| ::
                        && var slot := s.bn.attestations_submitted[i].data.slot;
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && s.bn.attestations_submitted[i].data == dvn.consensus_on_attestation_data[slot].decided_value.safe_get()
    }

    predicate old_duty_has_submitted_att_data_pred17_in_sec_3_6<D(!new, 0)>(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];            
            && s.latest_attestation_duty.isPresent()
            && forall duty: AttestationDuty |
                    && duty in s.all_rcvd_duties      
                    && duty.slot < s.latest_attestation_duty.safe_get().slot ::
                            exists j: nat ::
                                && 0 <= j
                                && j < |s.bn.attestations_submitted| 
                                && duty.slot == s.bn.attestations_submitted[j].data.slot
    }

    predicate AttConsensusDecided_is_decided_value_pred18_in_sec_3_7<D(!new, 0)>(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && forall slot: Slot, att_data: AttestationData | 
                    f_att_consensus_decided.requires(s, slot, att_data) ::
                        // && var s' := f_att_consensus_decided(s, slot, att_data).state;
                        && slot in dvn.consensus_on_attestation_data.Keys
                        && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                        && dvn.consensus_on_attestation_data[slot].decided_value.safe_get() == att_data                        
    }

    predicate local_active_consensus_instance_not_later_than_latest_duty_pred19a_in_sec_3_7<D(!new, 0)>(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && s.latest_attestation_duty.isPresent()
                ==> forall slot: Slot | slot in s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys ::    
                        slot <= s.latest_attestation_duty.safe_get().slot
    }

    predicate no_latest_duty_is_older_than_distributed_undecided_consensus_instance_pred19b_in_sec_3_7<D(!new, 0)>(dvn: DVState)        
    {        
        forall slot: Slot | slot in dvn.consensus_on_attestation_data.Keys ::
            !dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                ==> ( forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
                        && var s := dvn.honest_nodes_states[pubkey];
                        && s.latest_attestation_duty.isPresent()
                            ==> s.latest_attestation_duty.safe_get().slot <= slot
                    )
    }

    predicate strictly_monotonic_att_duties_queue_pred20_in_sec_3_7<D(!new, 0)>(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && forall i1: nat, i2: nat | 
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

    predicate constructable_set_of_att_shares_has_at_least_one_share_from_honest_node_pred21_in_sec_3_7<D(!new, 0)>(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && forall slot: Slot,
                      att_data: AttestationData,
                      att_shares: set<AttestationShare>,
                      aggregation_bits: seq<bool> | 
                            && slot in s.rcvd_attestation_shares.Keys
                            && (att_data, aggregation_bits) in s.rcvd_attestation_shares[slot].Keys
                            && att_data.slot == slot
                            && att_shares == s.rcvd_attestation_shares[slot][(att_data, aggregation_bits)] ::
                                    s.construct_signed_attestation_signature(att_shares).isPresent()
                                        ==>  exists share: AttestationShare,
                                                    pubkey1: BLSPubkey :: 
                                                        && share in att_shares 
                                                        && share.data == att_data                                                     
                                                        && is_honest_node(dvn, pubkey1)
                                                        && var s1 := dvn.honest_nodes_states[pubkey1];
                                                        && existing_share_from_node(att_shares, att_data, s1, slot)                                      
    }

    predicate no_missing_att_in_db_pred21_in_sec_3_7<D(!new, 0)>(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && s.latest_attestation_duty.isPresent() 
            && !s.current_attestation_duty.isPresent()            
                ==> forall slot: Slot |
                        && slot <= s.latest_attestation_duty.safe_get().slot
                        && slot in s.rcvd_attestation_shares.Keys ::
                                exists att_data: AttestationData,
                                       bits: seq<bool>,                                   
                                       att_shares: set<AttestationShare> ::                                        
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

    predicate no_missing_att_in_db_pred22_in_sec_3_7<D(!new, 0)>(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && s.latest_attestation_duty.isPresent()                   
                ==> forall slot: Slot |
                        && slot <= s.latest_attestation_duty.safe_get().slot
                        && slot in s.rcvd_attestation_shares.Keys ::
                                exists att_data: AttestationData,
                                       bits: seq<bool>,                                   
                                       att_shares: set<AttestationShare> ::                                        
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

/*
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
*/
    
    predicate pred24(dvn: DVState)
    {
        forall pubkey: BLSPubkey, att: Attestation :: 
            && is_honest_node(dvn, pubkey)
            && var s := dvn.honest_nodes_states[pubkey];
            && ( exists i: nat :: 
                    && 0 <= i 
                    && i < |s.bn.attestations_submitted|
                    && att == s.bn.attestations_submitted[i]
               )
            && ( exists att_data: AttestationData, bits: seq<bool>, k: Slot ::
                    && k in s.rcvd_attestation_shares.Keys
                    && (att_data, bits) in s.rcvd_attestation_shares[k].Keys
                    && s.construct_signed_attestation_signature(
                            s.rcvd_attestation_shares[k][(att_data, bits)]).isPresent()
                    && att.signature == s.construct_signed_attestation_signature(
                                            s.rcvd_attestation_shares[k][(att_data, bits)]).safe_get()
               )
                ==> exists pubkey1: BLSPubkey, att_data: AttestationData, bits: seq<bool>, k: Slot ::
                        && is_honest_node(dvn, pubkey1)   
                        && k in s.rcvd_attestation_shares.Keys
                        && (att_data, bits) in s.rcvd_attestation_shares[k].Keys
                        && existing_share_from_node(
                                s.rcvd_attestation_shares[k][(att_data, bits)],
                                att_data,
                                s,
                                k)           
    } 

    predicate pred25_in_sec_3_7<D(!new, 0)>(dvn: DVState)   
    {
        forall i: Slot, p: AttestationData -> bool | 
            && i in dvn.consensus_on_attestation_data.Keys
            && p in dvn.consensus_on_attestation_data[i].honest_nodes_validity_functions ::
                forall att_data: AttestationData ::
                    p(att_data) 
                        ==> exists duty: AttestationDuty,    
                                   db: set<SlashingDBAttestation>,                         
                                   pubkey: BLSPubkey ::
                                        && is_honest_node(dvn, pubkey)                                         
                                        && var s := dvn.honest_nodes_states[pubkey];                                        
                                        && duty in s.all_rcvd_duties
                                        && consensus_is_valid_attestation_data(db, att_data, duty)
                                        && att_data.slot == i
                                        && db <= s.attestation_slashing_db
                                        && forall j: Slot | 
                                                && j <= i 
                                                && ( exists d :: d in s.all_rcvd_duties && d.slot == j ) ::
                                                        && dvn.consensus_on_attestation_data[j].decided_value.isPresent()
                                                        && ( exists db_att: SlashingDBAttestation, data: AttestationData :: 
                                                                && db_att in db
                                                                && data.slot == j
                                                                && db_att.signing_root == Some(hash_tree_root(data)) )
                                                        && ( forall db_att: SlashingDBAttestation, data: AttestationData :: 
                                                                && db_att in db
                                                                && data.slot == j                                                                
                                                                        ==> data == dvn.consensus_on_attestation_data[j].decided_value.safe_get() )                                                        
    }   

    

    predicate sent_att_share_from_honest_node_pred26_in_sec_3_7<D(!new, 0)>(dvn: DVState)        
    {
        forall att_share: AttestationShare :: 
            && att_share in dvn.att_network.allMessagesSent
            && ( exists pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
                    && var s := dvn.honest_nodes_states[pubkey];
                    && var epoch := compute_start_slot_at_epoch(att_share.data.target.epoch);
                    && var fork_version := bn_get_fork_version(epoch);
                    && var root := compute_attestation_signing_root(att_share.data, fork_version);
                    && att_share.signature == rs_sign_attestation(att_share.data, 
                                                  fork_version, 
                                                  root, 
                                                  s.rs)
               )
                    ==> ( && dvn.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent()
                          && att_share.data == dvn.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get()
                        )
               
    }

    predicate undecided_dist_consensus_instance_implies_latest_att_duty_pred27_in_sec_3_7<D(!new, 0)>(dvn: DVState)        
    {
        exists slot: Slot ::
            && slot in dvn.consensus_on_attestation_data.Keys
            && !dvn.consensus_on_attestation_data[slot].decided_value.isPresent() 
                ==> && ( forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
                            && var s := dvn.honest_nodes_states[pubkey];
                            && s.latest_attestation_duty.isPresent()
                                    ==> s.latest_attestation_duty.safe_get().slot <= slot
                       )
    }

    predicate at_most_one_undecided_dist_consensus_instance_pred28_in_sec_3_7<D(!new, 0)>(dvn: DVState)        
    {
        exists slot1: Slot, slot2: Slot ::
            && slot1 in dvn.consensus_on_attestation_data.Keys
            && slot2 in dvn.consensus_on_attestation_data.Keys
            && !dvn.consensus_on_attestation_data[slot1].decided_value.isPresent() 
            && !dvn.consensus_on_attestation_data[slot2].decided_value.isPresent() 
                ==> slot1 == slot2
    }

/*
    predicate fixed_set_all_nodes_in_sec_3_7<D(!new, 0)>(
        s: DVCNodeState, 
        e: Types.Event,
        s': DVCNodeState)
    requires f_process_event.requires(s, e)
    {
        s' == DVCNode_Spec.f_process_event(s, e).state ==> s.peers == s'.peers                
    }
    */
}