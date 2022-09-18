include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/helper_sets_lemmas.dfy"



module Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Helper_Sets_Lemmas


    // For every pair (n1, n2) of honest nodes working for the same attestation duty, 
    // either both n1 and n2 decides on the same data or one of them has not decided yet.
    predicate inv1_in_sec_3_1_no_conflict_decisions<D(!new, 0)>(s: ConsensusInstance<D>)
    {
        forall n1: BLSPubkey, n2: BLSPubkey | 
            && ConsensusSpec.isConditionForSafetyTrue(s)
            && n1 in s.honest_nodes_status.Keys
            && n2 in s.honest_nodes_status.Keys ::                         
                    || s.honest_nodes_status[n1] == NOT_DECIDED
                    || s.honest_nodes_status[n2] == NOT_DECIDED
                    || s.honest_nodes_status[n1] == s.honest_nodes_status[n2]
    }

    // If a consensus instance has not decided, no honest nodes have not decided.
    predicate inv2_in_sec_3_1_no_decisions<D(!new, 0)>(s: ConsensusInstance<D>)
    {
        && ConsensusSpec.isConditionForSafetyTrue(s)
        && !s.decided_value.isPresent()
                ==> ( forall i: BLSPubkey | i in s.honest_nodes_status.Keys ::
                                    s.honest_nodes_status[i] == NOT_DECIDED
                    )                
    }

    predicate is_honest_node(s: DVState, n: BLSPubkey)
    {
        // && n in s.all_nodes
        // && !(n in s.adversary.nodes)
        && n in s.honest_nodes_states.Keys
    }

    predicate att_shares_from_same_att_data(s1: AttestationShare, s2: AttestationShare)
    {
        && s1.data == s2.data
        && s1.aggregation_bits == s2.aggregation_bits
    }

    predicate isFromQuorum<D(!new, 0)>(dvn: DVState, S: set<D>)
    {
        quorum(|dvn.all_nodes|) <= |S|
    }

    // For every pair (db1, db2) of slashing attestation databases of two honest nodes, 
    // db1 is a subset of db2 or db2 is a subset of db1.
    predicate inv3_in_sec_3_2_consistant_att_slashing_databases_between_honest_nodes(s: DVState)
    {
        forall n1: BLSPubkey, n2: BLSPubkey |
            && is_honest_node(s, n1)
            && is_honest_node(s, n2) ::
                inv3_in_sec_3_2_body(s, n1, n2)
    }

    predicate inv3_in_sec_3_2_body(s: DVState, n1: BLSPubkey, n2: BLSPubkey)
    {
        && is_honest_node(s, n1)
        && is_honest_node(s, n2) 
        && ( || s.honest_nodes_states[n1].attestation_slashing_db <= s.honest_nodes_states[n2].attestation_slashing_db
             || s.honest_nodes_states[n2].attestation_slashing_db <= s.honest_nodes_states[n1].attestation_slashing_db
           )                   
    }

    // For every record r in a slashing db of an honest node, 
    // there exist an attestation duty and an attestation data such that
    //      - The node has received the duty.
    //      - The data is for the attestation.
    //      - The data and the duty are for the same slot.
    //      - The data is not slashable in db - {r}.    
    predicate pred4_in_sec_3_2_consistant_slashing_db(dvn: DVState)
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var nState := dvn.honest_nodes_states[pubkey];
            && var db := nState.attestation_slashing_db;
            && forall dbRecord: SlashingDBAttestation | dbRecord in db ::
                    pred4_in_sec_3_2_body(dvn, pubkey, dbRecord)      
    }

    /*
    predicate pred4_in_sec_3_2_consistant_attestations_in_one_slashing_db(dvn: DVState)
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
*/

    predicate pred4_in_sec_3_2_body(dvn: DVState, pubkey: BLSPubkey, dbRecord: SlashingDBAttestation)
    {
        && is_honest_node(dvn, pubkey) 
        && var nState := dvn.honest_nodes_states[pubkey];
        && var db := nState.attestation_slashing_db;
        && dbRecord in db 
        && exists att_data: AttestationData, 
                  att_duty: AttestationDuty ::
                        && att_duty in nState.all_rcvd_duties                        
                        && att_data.slot == att_duty.slot 
                        && is_SlashingDBAtt_for_given_att_data(dbRecord, att_data)
                        && var S := db - { dbRecord };
                        && !is_slashable_attestation_data(S, att_data)
    }

    // If the current duty is not none, then the lastest served duty is the current duty.
    predicate old_inv5(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && old_inv5_body(s)            
    }

    predicate old_inv5_body(hn_state: DVCNodeState)        
    {
        hn_state.current_attestation_duty.isPresent()
            ==> ( && hn_state.latest_attestation_duty.isPresent()
                  && hn_state.current_attestation_duty.safe_get() == hn_state.latest_attestation_duty.safe_get()
                )
    }

    predicate exisiting_consensus_instance_for_curr_att_duty_pred6_in_sec_3_3(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && s.current_attestation_duty.isPresent()
                    ==> s.current_attestation_duty.safe_get().slot 
                            in s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys 
    }

    predicate active_consensus_instances_imples_existence_of_curr_att_duty_pred7_in_sec_3_3(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys != {}
                    ==> ( && s.current_attestation_duty.isPresent()
                          && s.current_attestation_duty.safe_get().slot 
                                in s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys 
                        )
    }
    
    predicate queued_duties_later_than_curr_att_duty_pred8_in_sec_3_3(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && s.current_attestation_duty.isPresent()
                    ==> forall queued_duty: AttestationDuty | queued_duty in s.attestation_duties_queue :: 
                            s.current_attestation_duty.safe_get().slot < queued_duty.slot
    }

    predicate submitted_att_by_curr_att_duty_pred9_in_sec_3_3(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && s.current_attestation_duty.isPresent()
                    ==> forall i: nat | 0 <= i && i < |s.bn.attestations_submitted| ::
                            s.bn.attestations_submitted[i].data.slot <= s.current_attestation_duty.safe_get().slot
    }

    predicate old_inv10_body(s: DVCNodeState)
    {
        !s.latest_attestation_duty.isPresent()
            ==> s.attestation_duties_queue == [] 
    }

    predicate old_inv10(dvn: DVState)        
    {
        forall pubkey: BLSPubkey :: 
            && is_honest_node(dvn, pubkey) 
            && var s := dvn.honest_nodes_states[pubkey];
            && old_inv10_body(s)
    }

    predicate queued_duties_later_than_latest_att_duty_pred11_in_sec_3_4(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && s.latest_attestation_duty.isPresent()
                    ==> forall queued_duty: AttestationDuty | queued_duty in s.attestation_duties_queue :: 
                            s.latest_attestation_duty.safe_get().slot < queued_duty.slot
    }

    predicate submitted_att_by_latest_att_duty_pred12_in_sec_3_4(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && s.latest_attestation_duty.isPresent()
                    ==> forall i: nat | 0 <= i && i < |s.bn.attestations_submitted| ::
                            s.bn.attestations_submitted[i].data.slot <= s.latest_attestation_duty.safe_get().slot
    }

    predicate active_consensus_instances_for_slots_until_latest_att_duty_pred13_in_sec_3_4(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && s.latest_attestation_duty.isPresent()
                    ==> forall i: Slot | i in s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys ::
                            i <= s.latest_attestation_duty.safe_get().slot
    }

    predicate no_active_consensus_instances_for_queued_att_duties_pred14_in_sec_3_5(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && forall i: Slot, j: nat | 
                    && i in s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys 
                    && 0 <= j
                    && j < |s.attestation_duties_queue| ::
                        i < s.attestation_duties_queue[j].slot
    }

    predicate at_most_one_active_consensus_instances_has_not_decided_pred15_in_sec_3_5(dvn: DVState)        
    {
        forall pubkey: BLSPubkey |
            is_honest_node(dvn, pubkey) ::
                && var s := dvn.honest_nodes_states[pubkey];
                && forall i: Slot, j: Slot ::
                    ( && i in s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys 
                      && j in s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys 
                      && var ci_i := s.attestation_consensus_engine_state.attestation_consensus_active_instances[i];
                      && var ci_j := s.attestation_consensus_engine_state.attestation_consensus_active_instances[j];
                      && ( exists di: AttestationData, dj: AttestationData ::
                            && ci_i.validityPredicate(di)
                            && ci_j.validityPredicate(dj)
                         )
                    )
                        ==> i == j                             
    }
    

    predicate att_from_imported_block_is_decided_value_pred16_in_sec_3_6(dvn: DVState)        
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

    predicate old_duty_has_submitted_att_data_pred17_in_sec_3_6(dvn: DVState)        
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

    predicate AttConsensusDecided_is_decided_value_pred18_in_sec_3_7(dvn: DVState)        
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

    predicate local_active_consensus_instance_not_later_than_latest_duty_pred19a_in_sec_3_7(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && s.latest_attestation_duty.isPresent()
                ==> forall slot: Slot | slot in s.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys ::    
                        slot <= s.latest_attestation_duty.safe_get().slot
    }

    predicate no_latest_duty_is_older_than_distributed_undecided_consensus_instance_pred19b_in_sec_3_7(dvn: DVState)        
    {        
        forall slot: Slot | slot in dvn.consensus_on_attestation_data.Keys ::
            !dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                ==> ( forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
                        && var s := dvn.honest_nodes_states[pubkey];
                        && s.latest_attestation_duty.isPresent()
                            ==> s.latest_attestation_duty.safe_get().slot <= slot
                    )
    }

    predicate strictly_monotonic_att_duties_queue_pred20_in_sec_3_7(dvn: DVState)        
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
               epoch: Epoch ::
                    && var start_slot := compute_start_slot_at_epoch(epoch);
                    && var fork_version := bn_get_fork_version(slot);
                    && var root := compute_attestation_signing_root(att_data, fork_version);
                    && var att_sig := rs_sign_attestation(att_data, fork_version, root, s.rs);
                    && share in att_shares
                    && share.data == att_data
                    && share.signature == att_sig
                    && fork_version == bn_get_fork_version(att_data.slot)                                                                                
    }

    predicate constructable_set_of_att_shares_has_at_least_one_share_from_honest_node_pred21_in_sec_3_7(dvn: DVState)        
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

    predicate no_missing_att_in_db_pred22_in_sec_3_7(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && s.latest_attestation_duty.isPresent() 
            && !s.current_attestation_duty.isPresent()            
                ==> ( forall slot: Slot, att_data: AttestationData ::
                        ( && slot <= s.latest_attestation_duty.safe_get().slot
                          && slot in s.rcvd_attestation_shares.Keys 
                          && exists bits: seq<bool>,                                   
                                    att_shares: set<AttestationShare> ::                                        
                                        && (att_data, bits) in s.rcvd_attestation_shares[slot].Keys
                                        && att_data.slot == slot
                                        && att_shares == s.rcvd_attestation_shares[slot][(att_data, bits)]
                                        && s.construct_signed_attestation_signature(att_shares).isPresent() 
                                        && (forall share: AttestationShare ::
                                                    share in att_shares ==> share.data == att_data )
                        )
                            ==> exists slashingdbAtt: SlashingDBAttestation ::
                                    && slashingdbAtt in s.attestation_slashing_db            
                                    && Some(hash_tree_root(att_data)) == slashingdbAtt.signing_root
                    )
    }

    predicate no_missing_att_in_db_pred23_in_sec_3_7(dvn: DVState)        
    {
        forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
            && var s := dvn.honest_nodes_states[pubkey];
            && s.latest_attestation_duty.isPresent()                   
                ==> ( forall slot: Slot, att_data: AttestationData ::
                        ( && slot < s.latest_attestation_duty.safe_get().slot
                          && slot in s.rcvd_attestation_shares.Keys 
                          && ( exists bits: seq<bool>,                                   
                                      att_shares: set<AttestationShare> ::                                        
                                            && (att_data, bits) in s.rcvd_attestation_shares[slot].Keys
                                            && att_data.slot == slot
                                            && att_shares == s.rcvd_attestation_shares[slot][(att_data, bits)]
                                            && s.construct_signed_attestation_signature(att_shares).isPresent() 
                                            && (forall share: AttestationShare ::
                                                    share in att_shares ==> share.data == att_data )
                             )
                        )
                            ==> exists slashingdbAtt: SlashingDBAttestation ::
                                            && slashingdbAtt in s.attestation_slashing_db            
                                            && Some(hash_tree_root(att_data)) == slashingdbAtt.signing_root
                    )
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

    // Type eroors after changing the type of honest_nodes_validity_functions in consensus
    // predicate pred25_in_sec_3_7(dvn: DVState)   
    // {
    //     forall i: Slot, p: AttestationData -> bool | 
    //         && i in dvn.consensus_on_attestation_data.Keys
    //         && p in dvn.consensus_on_attestation_data[i].honest_nodes_validity_functions ::
    //             forall att_data: AttestationData ::
    //                 p(att_data) 
    //                     ==> exists duty: AttestationDuty,    
    //                                db: set<SlashingDBAttestation>,                         
    //                                pubkey: BLSPubkey ::
    //                                     && is_honest_node(dvn, pubkey)                                         
    //                                     && var s := dvn.honest_nodes_states[pubkey];                                        
    //                                     && duty in s.all_rcvd_duties
    //                                     && consensus_is_valid_attestation_data(db, att_data, duty)
    //                                     && att_data.slot == i
    //                                     && db <= s.attestation_slashing_db
    //                                     && forall j: Slot | 
    //                                             && j <= i 
    //                                             && ( exists d :: d in s.all_rcvd_duties && d.slot == j ) ::
    //                                                     && dvn.consensus_on_attestation_data[j].decided_value.isPresent()
    //                                                     && ( exists db_att: SlashingDBAttestation, data: AttestationData :: 
    //                                                             && db_att in db
    //                                                             && data.slot == j
    //                                                             && db_att.signing_root == Some(hash_tree_root(data)) )
    //                                                     && ( forall db_att: SlashingDBAttestation, data: AttestationData :: 
    //                                                             && db_att in db
    //                                                             && data.slot == j                                                                
    //                                                                     ==> data == dvn.consensus_on_attestation_data[j].decided_value.safe_get() )                                                        
    // }   

    

    predicate sent_att_share_from_honest_node_pred26_in_sec_3_7(dvn: DVState)        
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

    predicate undecided_dist_consensus_instance_implies_latest_att_duty_pred27_in_sec_3_7(dvn: DVState)        
    {
        forall slot: Slot ::
            && slot in dvn.consensus_on_attestation_data.Keys
            && !dvn.consensus_on_attestation_data[slot].decided_value.isPresent() 
                ==> && ( forall pubkey: BLSPubkey | is_honest_node(dvn, pubkey) ::
                            && var s := dvn.honest_nodes_states[pubkey];
                            && s.latest_attestation_duty.isPresent()
                                    ==> s.latest_attestation_duty.safe_get().slot <= slot
                       )
    }

    predicate at_most_one_undecided_dist_consensus_instance_pred28_in_sec_3_7(dvn: DVState)        
    {
        forall slot1: Slot, slot2: Slot ::
            && slot1 in dvn.consensus_on_attestation_data.Keys
            && slot2 in dvn.consensus_on_attestation_data.Keys
            && !dvn.consensus_on_attestation_data[slot1].decided_value.isPresent() 
            && !dvn.consensus_on_attestation_data[slot2].decided_value.isPresent() 
                ==> slot1 == slot2
    }

    predicate shared_rcvd_att_duties_pred29_in_sec_3_7(dvn: DVState)        
    {
        forall p1: BLSPubkey, p2: BLSPubkey ::
            && is_honest_node(dvn, p1)            
            && is_honest_node(dvn, p2)
                ==> && var s1 := dvn.honest_nodes_states[p1];
                    && var s2 := dvn.honest_nodes_states[p2];
                    && ( || s1.all_rcvd_duties <= s2.all_rcvd_duties
                         || s2.all_rcvd_duties <= s1.all_rcvd_duties
                       )                
    }

    predicate same_function_to_reconstruct_attestations_pred30_in_sec_3_7(dvn: DVState)        
    {
        forall pubkey: BLSPubkey ::
            is_honest_node(dvn, pubkey)            
                ==> && var s := dvn.honest_nodes_states[pubkey];
                    && s.construct_signed_attestation_signature == dvn.construct_signed_attestation_signature
                    

    }

    predicate shared_attestations_pred31_in_sec_3_7(dvn: DVState)        
    {
        forall p1: BLSPubkey, p2: BLSPubkey ::
            && is_honest_node(dvn, p1)            
            && is_honest_node(dvn, p2)
                ==> && var s1 := dvn.honest_nodes_states[p1];
                    && var s2 := dvn.honest_nodes_states[p2];
                    && ( || s1.attestation_slashing_db <= s2.attestation_slashing_db
                         || s2.attestation_slashing_db <= s1.attestation_slashing_db
                       )                
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

    predicate att_signed_by_dv_always_was_submitted_by_honest_node_pred33_in_sec_3_8(dvn: DVState)
    {
        forall att: Attestation |
            att in dvn.globally_signed_attestations ::
                exists pubkey: BLSPubkey, share: AttestationShare, S: set<AttestationShare> ::
                    && is_honest_node(dvn, pubkey)
                    && var s := dvn.honest_nodes_states[pubkey];
                    && share in dvn.all_att_shares
                    && is_owner_of_att_share(share, s)
                    && S <= dvn.all_att_shares
                    && dvn.construct_signed_attestation_signature(S).isPresent()
                    && dvn.construct_signed_attestation_signature(S).safe_get() == att.signature
    }

    predicate no_slashable_record_in_slashingDB_of_honset_node_pred34_in_sec_3_8(dvn: DVState)
    {
        forall pubkey: BLSPubkey |
            is_honest_node(dvn, pubkey) ::
                && var s := dvn.honest_nodes_states[pubkey];
                && forall dbRecord: SlashingDBAttestation |
                    dbRecord in s.attestation_slashing_db ::
                        && var S := s.attestation_slashing_db - {dbRecord}; 
                        && exists att_data: AttestationData ::
                                && is_SlashingDBAtt_for_given_att_data(dbRecord, att_data)
                                && !is_slashable_attestation_data(S, att_data)
    }

    predicate matching_sent_att_shares_and_slashingDB_pred35_in_sec_3_8(dvn: DVState)
    {
        forall pubkey: BLSPubkey |
            is_honest_node(dvn, pubkey) ::
                && var s := dvn.honest_nodes_states[pubkey];
                && forall share: AttestationShare |
                    && share in dvn.all_att_shares 
                    && is_owner_of_att_share(share, s) ::
                        ( exists dbRecord: SlashingDBAttestation ::
                                && dbRecord in s.attestation_slashing_db
                                && is_SlashingDBAtt_for_given_att_data(dbRecord, share.data)
                        )
    }

    predicate subseteq_relationship_between_slashingDBes_of_honest_nodes_pred36_in_sec_3_8(dvn: DVState)
    {
        forall p1, p2: BLSPubkey |
            && is_honest_node(dvn, p1)
            && is_honest_node(dvn, p2) ::
                && var s1 := dvn.honest_nodes_states[p1];
                && var s2 := dvn.honest_nodes_states[p2];
                && var db1 := s1.attestation_slashing_db;
                && var db2 := s2.attestation_slashing_db;
                && ( || db1 <= db2
                     || db2 <= db1
                   )
    }

    predicate always_keep_track_of_highest_slot_with_dvn_signed_att(dvn: DVState)
    {
        && ( dvn.globally_signed_attestations != {}
               <==> dvn.highest_slot_with_dvn_signed_att.isPresent())
        && dvn.highest_slot_with_dvn_signed_att.isPresent()
                ==> exists att: Attestation ::
                        && att in dvn.globally_signed_attestations
                        && att.data.slot == dvn.highest_slot_with_dvn_signed_att.safe_get()
    }

    predicate signed_att_by_dv_has_enough_shares(dvn: DVState)
    {
        forall att: Attestation |
            att in dvn.globally_signed_attestations ::
                exists S: set<AttestationShare> ::
                    && S <= dvn.all_att_shares
                    && dvn.construct_signed_attestation_signature(S).isPresent()
                    && att.signature == dvn.construct_signed_attestation_signature(S).safe_get()                        
    }

    predicate constructable_set_of_att_shares_requires_shares_from_honest_nodes(dvn: DVState)
    {
        forall S: set<AttestationShare> ::
            dvn.construct_signed_attestation_signature(S).isPresent()
                ==> exists pubkey: BLSPubkey, share: AttestationShare ::
                        && share in S
                        && is_honest_node(dvn, pubkey)
                        && var s := dvn.honest_nodes_states[pubkey];
                        && is_owner_of_att_share(share, s)
    }
/*
    predicate pred37_in_sec_3_8(dvn: DVState)
    {
          && dvn.highest_slot_with_dvn_signed_att.isPresent()
          && always_keep_track_of_highest_slot_with_dvn_signed_att(dvn)
          && exists a: Attestation :: a in dvn.globally_signed_attestations
          && get_attestation_with_given_slot.requires(
                    dvn.globally_signed_attestations,
                    dvn.highest_slot_with_dvn_signed_att.safe_get()
                )
          && var a_max := get_attestation_with_given_slot(
                    dvn.globally_signed_attestations,
                    dvn.highest_slot_with_dvn_signed_att.safe_get()
                );
          && signed_att_by_dv_has_enough_shares(dvn)
          && var S: set<AttestationShare> :|
                    && S <= dvn.all_att_shares
                    && dvn.construct_signed_attestation_signature(S).isPresent()
                    && a_max.signature == dvn.construct_signed_attestation_signature(S).safe_get();
          && constructable_set_of_att_shares_has_at_least_one_share_from_honest_node_pred21_in_sec_3_7(dvn)
          && var pubkey: BLSPubkey :|
                && is_honest_node(dvn, pubkey)
                && var s := dvn.honest_nodes_states[pubkey];
                && exists share: AttestationShare ::
                        && share in S
                        && is_owner_of_att_share(share, s);
          && var s := dvn.honest_nodes_states[pubkey];
          && dvn.globally_signed_attestations <= seqToSet(s.bn.attestations_submitted)                
    }
*/

    predicate pred37a_in_sec_3_8(dvn: DVState)
    {
        forall att: Attestation |
            att in dvn.globally_signed_attestations ::
                exists pubkey: BLSPubkey, 
                       share: AttestationShare,
                       S: set<AttestationShare> ::
                    && is_honest_node(dvn, pubkey)
                    && var s := dvn.honest_nodes_states[pubkey];
                    && is_owner_of_att_share(share, s)
                    && share in dvn.all_att_shares
                    && share.data == att.data
                    && share in S
                    && dvn.construct_signed_attestation_signature(S).isPresent()
                    && var sign := dvn.construct_signed_attestation_signature(S).safe_get();
                    && sign == att.signature
    }

    predicate pred37b_in_sec_3_8(dvn: DVState)
    {
        forall pubkey: BLSPubkey |
            is_honest_node(dvn, pubkey) ::
                && var s := dvn.honest_nodes_states[pubkey];
                && forall att: Attestation |
                    att in s.bn.attestations_submitted ::
                        forall duty: AttestationDuty ::
                            && duty.slot < att.data.slot 
                            && duty in s.all_rcvd_duties
                                ==> exists a: Attestation ::
                                        && a.data.slot == duty.slot
                                        && a in s.bn.attestations_submitted
    }

    predicate pred37c_in_sec_3_8(dvn: DVState) 
    {
        exists pubkey: BLSPubkey ::
            && is_honest_node(dvn, pubkey)
            && var s := dvn.honest_nodes_states[pubkey];
            && dvn.globally_signed_attestations <= seqToSet(s.bn.attestations_submitted)
    }


    predicate slashingDB_without_slashable_records(db: set<SlashingDBAttestation>)
    {
        exists dbRecord: SlashingDBAttestation, 
               att_data: AttestationData ::                                    
                    && is_SlashingDBAtt_for_given_att_data(dbRecord, att_data)
                    && var S := db - {dbRecord};
                    && !is_slashable_attestation_data(S, att_data)
    }

    predicate pred38_in_sec_3_8(dvn: DVState)
    {
        forall pubkey: BLSPubkey |
            is_honest_node(dvn, pubkey) ::
                && var s := dvn.honest_nodes_states[pubkey];
                && var db := s.attestation_slashing_db;
                && forall S: set<SlashingDBAttestation> |
                        S <= db ::
                            slashingDB_without_slashable_records(S)
                            
    }

    predicate existing_att_data_for_given_slashingDBAttestsation(dbRecord: SlashingDBAttestation)
    {
        exists att_data: AttestationData :: is_SlashingDBAtt_for_given_att_data(dbRecord, att_data)
    }

    predicate pred39_in_sec_3_8(dvn: DVState)
    {
        forall p1, p2: BLSPubkey |
            && is_honest_node(dvn, p1)
            && is_honest_node(dvn, p2) ::
                && var s1 := dvn.honest_nodes_states[p1];
                && var s2 := dvn.honest_nodes_states[p2];
                && var db1 := s1.attestation_slashing_db;
                && var db2 := s1.attestation_slashing_db;
                && db1 <= db2
                    ==> && ( forall dbRecord: SlashingDBAttestation | dbRecord in db1 ::
                                && existing_att_data_for_given_slashingDBAttestsation(dbRecord)
                                && var att_data: AttestationData :|
                                        is_SlashingDBAtt_for_given_att_data(dbRecord, att_data);
                                && !is_slashable_attestation_data(db2, att_data)

                           )
                        && ( forall dbRecord: SlashingDBAttestation | dbRecord in db2 - db1 ::
                                && existing_att_data_for_given_slashingDBAttestsation(dbRecord)
                                && var att_data: AttestationData :|
                                        is_SlashingDBAtt_for_given_att_data(dbRecord, att_data);
                                && !is_slashable_attestation_data(db1, att_data)

                           )          
    }

    predicate isSignedByDV(dvn: DVState, signed_att: Attestation)

    predicate isMaxSlotWithSignedAtt(dvn: DVState, s: Slot)
    {
        && ( forall att: Attestation ::
                att in dvn.globally_signed_attestations
                    ==> get_slot_from_att(att) <= s
           )
        && ( exists att: Attestation ::
                && att in dvn.globally_signed_attestations
                && get_slot_from_att(att) == s
           )
    }

    predicate checking_highest_slot_with_dvn_signed_att(dvn: DVState)
    {
        && dvn.highest_slot_with_dvn_signed_att.isPresent()
        && isMaxSlotWithSignedAtt(dvn, dvn.highest_slot_with_dvn_signed_att.safe_get())
    }

    predicate existingHonestWitnessForSigningAtt(dvn: DVState)
    {
        forall att: Attestation :: 
            att in dvn.globally_signed_attestations
                ==> ( exists pubkey: BLSPubkey ::
                        && is_honest_node(dvn, pubkey)
                        && var s := dvn.honest_nodes_states[pubkey];
                        && var shares := get_shares_in_set_based_on_given_att(dvn.all_att_shares, att);
                        && exists share: AttestationShare ::
                                ( && share in shares
                                  && is_owner_of_att_share(share, s)
                                )
                    )
    }

/*
    predicate existingHonestWitnessForSigningAttAtSlot(dvn: DVState, s: Slot)
    {
        exists pubkey: BLSPubkey ::
            && is_honest_node(dvn, pubkey)
            && var dvc := dvn.honest_nodes_states[pubkey];
            && var att := get_attestation_with_given_slot(dvn.globally_signed_attestations, s);
            && var shares := get_shares_in_set_based_on_given_att(dvn.all_att_shares, att);
            && exists share: AttestationShare ::
                                ( && share in shares
                                  && is_owner_of_att_share(share, dvc)
                                )            
    }
*/
/*
    predicate SlashingDBAttestation_of_honest_node_has_no_slashable_data(dvn: DVState)
    {
        forall pubkey: BLSPubkey |
            is_honest_node(dvn, pubkey) :: 
                && var s := dvn.honest_nodes_states[pubkey];
                && forall dbRecord: SlashingDBAttestation ::
                        dbRecord in s.attestation_slashing_db 
                            ==> ( && var other_records := s.attestation_slashing_db - {dbRecord}; 
                                  && var att_data := get_aDataFromSlashingDBAtt(dbRecord);
                                  && !is_slashable_attestation_data(other_records, att_data)   
                                )
    }    


    predicate WitnessForHighestAttHasAllGloballySignedAtt(dvn: DVState, pubkey: BLSPubkey)
    {
        && is_honest_node(dvn, pubkey)
        && var s := dvn.honest_nodes_states[pubkey];
        && dvn.globally_signed_attestations <= seqToSet(s.bn.attestations_submitted)
        && dvn.globally_slashing_db_attestations <= s.attestation_slashing_db
    }
*/

    predicate pred40_no_slaslable_attestation_in_any_subset_of_submitted_attestations(dvn: DVState)
    {
        forall pubkey: BLSPubkey |
            is_honest_node(dvn, pubkey) ::
                && var s := dvn.honest_nodes_states[pubkey];
                && var attSet := seqToSet(s.bn.attestations_submitted);
                && forall S: set<Attestation>, att: Attestation |
                    && S <= attSet 
                    && att in S ::
                        && var tempSet := S - { att };
                        && is_slashable_attestation_data_in_set_of_attestations(tempSet, att.data)
    }

/*
    predicate pred40(dvn: DVState)
    {
        forall pubkey: BLSPubkey ::,
            S: set<Attestation>, 
            a: Attestation ::
                && is_honest_node(dvn, pubkey)
                && var s := dvn.honest_nodes_states[pubkey];
                && var attSet := seqToSet(s.bn.attestations_submitted);        
                && S <= attSet 
                && a in attSet
                && a !in S  
                    ==> is_slashable_attestation_data_in_set_of_attestations(S, a.data)
    }
    */

    predicate pred40(dvn: DVState)
    {
        forall pubkey: BLSPubkey ::
            is_honest_node(dvn, pubkey) ==> pred40_body(dvn.honest_nodes_states[pubkey])                
    }


    predicate pred40_body(s: DVCNodeState)
    {
        forall S: set<Attestation>, a: Attestation ::                
            && var attSet := seqToSet(s.bn.attestations_submitted);
            (        
                && S <= attSet 
                && a in attSet
                && a !in S 
            )
                ==> !is_slashable_attestation_data_in_set_of_attestations(S, a.data)
    }

/*
    predicate old_safety(dvn: DVState)
    {
        forall signed_att: Attestation |
            && isSignedByDV(dvn, signed_att)
            && signed_att in dvn.globally_signed_attestations ::                
                && var dbAttRecord := construct_SlashingDBAttestation_from_att(signed_att);
                && var att_data := signed_att.data;
                && var otherDBAttRecords := dvn.globally_slashing_db_attestations - {dbAttRecord};  
                && !is_slashable_attestation_data(otherDBAttRecords, att_data)   
    }
*/

    predicate pred_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(
        dvn: DVState,
        dvc: DVCNodeState
    )
    {
        var rcvd_attestation_shares := dvc.rcvd_attestation_shares;

        forall i, j |
            && i in rcvd_attestation_shares.Keys 
            && j in rcvd_attestation_shares[i]
            ::
            rcvd_attestation_shares[i][j] <= dvn.att_network.allMessagesSent
    }

    predicate pred_rcvd_attestation_shares_is_in_all_messages_sent_single_node(
        dvn: DVState,
        n: BLSPubkey
    )
    requires n in dvn.honest_nodes_states.Keys
    {
        pred_rcvd_attestation_shares_is_in_all_messages_sent_single_node_state(
            dvn,
            dvn.honest_nodes_states[n]
        )
    }

    predicate pred_rcvd_attestation_shares_is_in_all_messages_sent(
        dvn: DVState    
    )
    {
        forall n |
            n in dvn.honest_nodes_states
            ::
            pred_rcvd_attestation_shares_is_in_all_messages_sent_single_node(dvn, n)
    }  

    // predicate pred_attestations_signature_by_honest_node_implies_existence_of_attestation_with_correct_data_helper_helper(
    //     dvn: DVState,
    //     att_share: AttestationShare,
    //     signing_root: Root,
    //     signature: BLSSignature
    // )      
    // {
    //     && att_share in dvn.att_network.allMessagesSent
    //     && att_share.signature == signature
    //     && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));
    //     && signing_root == compute_attestation_signing_root(att_share.data, fork_version)
    // }

    // predicate pred_attestations_signature_by_honest_node_implies_existence_of_attestation_with_correct_data_helper(
    //     dvn: DVState,
    //     att_share: AttestationShare,
    //     hn: BLSPubkey,
    //     signing_root: Root
    // )
    // {
    //     && att_share in dvn.att_network.allMessagesSent
    //     && hn in dvn.honest_nodes_states.Keys
    //     && verify_bls_siganture(signing_root, att_share.signature, hn)
    // }

    // predicate pred_attestations_signature_by_honest_node_implies_existence_of_attestation_with_correct_data(
    //     dvn: DVState
    // )
    // {
    //     forall att_share, signing_root, hn |
    //             pred_attestations_signature_by_honest_node_implies_existence_of_attestation_with_correct_data_helper(
    //                 dvn,
    //                 att_share,
    //                 hn,
    //                 signing_root
    //             )
    //         ::
    //         exists att_share' :: pred_attestations_signature_by_honest_node_implies_existence_of_attestation_with_correct_data_helper_helper(dvn, att_share', signing_root, att_share.signature)

    // }    

    predicate pred_4_1_b_exists(
        dvn: DVState,
        hn': BLSPubkey, 
        att_share: AttestationShare,
        a: Attestation
    )
    {
        && hn' in dvn.honest_nodes_states.Keys 
        && att_share in dvn.att_network.allMessagesSent
        && att_share.data == a.data
        && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));
        && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
        && verify_bls_siganture(attestation_signing_root, att_share.signature, hn')
    }

    predicate pred_4_1_b(dvn: DVState)
    {
        forall hn, a |
            && hn in dvn.honest_nodes_states.Keys 
            && a in dvn.honest_nodes_states[hn].bn.attestations_submitted
            ::
            exists hn', att_share: AttestationShare :: pred_4_1_b_exists(dvn, hn', att_share, a)
    }

    predicate pred_4_1_c(dvn: DVState)
    {
        forall hn, att_share |
                && hn in dvn.honest_nodes_states.Keys 
                && att_share in dvn.att_network.allMessagesSent
                && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(att_share.data.target.epoch));                
                && var attestation_signing_root := compute_attestation_signing_root(att_share.data, fork_version);
                && verify_bls_siganture(attestation_signing_root, att_share.signature, hn)
            ::
                && dvn.consensus_on_attestation_data[att_share.data.slot].decided_value.isPresent()
                && dvn.consensus_on_attestation_data[att_share.data.slot].decided_value.safe_get() == att_share.data
    }  

    predicate pred_4_1_f_a(dvn: DVState)
    {
        forall cid |
            && cid in dvn.consensus_on_attestation_data.Keys
            && dvn.consensus_on_attestation_data[cid].decided_value.isPresent()
            ::
            is_a_valid_decided_value(dvn.consensus_on_attestation_data[cid])
    }  


    predicate pred_4_1_f_b(dvn: DVState)
    {
        forall cid |
            && cid in dvn.consensus_on_attestation_data.Keys
            && dvn.consensus_on_attestation_data[cid].decided_value.isPresent()
            ::
            dvn.consensus_on_attestation_data[cid].decided_value.safe_get().slot == cid
    }     

    predicate pred_4_1_g_i_for_dvc_single_dvc(
        dvn: DVState,
        n: BLSPubkey,
        cid: Slot
    )
    requires n in dvn.honest_nodes_states.Keys 
    requires cid in dvn.honest_nodes_states[n].attestation_consensus_engine_state.attestation_consensus_active_instances
    {
        var dvc := dvn.honest_nodes_states[n];
        var acvc := dvc.attestation_consensus_engine_state.attestation_consensus_active_instances[cid];

        pred_4_1_g_i_for_dvc_single_dvc_2_body_body(
            cid, 
            acvc.attestation_duty, 
            acvc.validityPredicate
        ) 
    }

    predicate pred_4_1_g_i_for_dvc_single_dvc_2_body(
        dvc: DVCNodeState,
        cid: Slot
    )
    requires cid in dvc.attestation_consensus_engine_state.attestation_consensus_active_instances
    {
        var acvc := dvc.attestation_consensus_engine_state.attestation_consensus_active_instances[cid];
        pred_4_1_g_i_for_dvc_single_dvc_2_body_body(
            cid, 
            acvc.attestation_duty, 
            acvc.validityPredicate
        ) 
    }     

    predicate pred_4_1_g_i_for_dvc_single_dvc_2_body_body(
        cid: Slot,
        attestation_duty: AttestationDuty,
        vp: AttestationData -> bool
    )
    {
        exists attestation_slashing_db ::
            pred_4_1_g_i_body(cid, attestation_duty, attestation_slashing_db, vp)        
    }         

    predicate pred_4_1_g_i_for_dvc_single_dvc_2(
        dvc: DVCNodeState
    )
    {
        forall cid | 
            && cid in dvc.attestation_consensus_engine_state.attestation_consensus_active_instances
            ::
            pred_4_1_g_i_for_dvc_single_dvc_2_body(dvc, cid)        
    }    

    predicate pred_4_1_g_i_for_dvc(
        dvn: DVState
    )
    {
        forall n, cid | 
            && n in dvn.honest_nodes_states 
            && cid in dvn.honest_nodes_states[n].attestation_consensus_engine_state.attestation_consensus_active_instances
            ::
            pred_4_1_g_i_for_dvc_single_dvc(dvn, n, cid)
    }

   
    predicate pred_4_1_g_i_body(
        s: Slot,
        attestation_duty: AttestationDuty,
        attestation_slashing_db: set<SlashingDBAttestation>,
        vp: AttestationData -> bool
    )
    {
        && attestation_duty.slot == s
        && (vp == (ad: AttestationData) => consensus_is_valid_attestation_data(attestation_slashing_db, ad, attestation_duty))
    }

    predicate pred_4_1_g_i(dvn: DVState)
    {
        forall hn, s: nat, vp |
            && hn in dvn.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
            && vp in dvn.consensus_on_attestation_data[s].honest_nodes_validity_functions[hn]
            ::
            exists attestation_duty, attestation_slashing_db ::
                pred_4_1_g_i_body(s, attestation_duty, attestation_slashing_db, vp)
    }

    // predicate pred_4_1_g_ii_body(dvn: DVState, hn: BLSPubkey, 
    //                              s1: Slot, s2: Slot, 
    //                              vp: AttestationData -> bool, 
    //                              db2: set<SlashingDBAttestation>,
    //                              sdba: SlashingDBAttestation)    
    // requires 
    //         && hn in dvn.honest_nodes_states.Keys
    //         && var hn_state := dvn.honest_nodes_states[hn];
    //         && s2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys            
    //         && s1 < s2
    //         && hn in dvn.consensus_on_attestation_data[s1].honest_nodes_validity_functions.Keys
    //         && hn in dvn.consensus_on_attestation_data[s2].honest_nodes_validity_functions.Keys
    //         // Another invariant to prove the two following lines
    //         && vp in dvn.consensus_on_attestation_data[s2].honest_nodes_validity_functions[hn]        
    //         && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys   
    //         && inv47_body(dvn, hn, s2) 
    //         && db2 == hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp]
    //         && dvn.consensus_on_attestation_data[s1].decided_value.isPresent()
    //         && dvn.consensus_on_attestation_data[s1].decided_value.isPresent()
    //         && var decided_a_data := dvn.consensus_on_attestation_data[s1].decided_value.safe_get();
    //         && sdba == construct_SlashingDBAttestation_from_att_data(decided_a_data)
    // {
    //     // && var hn_state := dvn.honest_nodes_states[hn];            
    //     // && var duty2: AttestationDuty :| duty2 in hn_state.all_rcvd_duties && duty2.slot == s2;
    //     // && vp == (ad: AttestationData) => consensus_is_valid_attestation_data(db2, ad, duty2)      
    //     /*      
    //     && dvn.consensus_on_attestation_data[s1].decided_value.isPresent()
    //     && var decided_a_data := dvn.consensus_on_attestation_data[s1].decided_value.safe_get();
    //     && var sdba := construct_SlashingDBAttestation_from_att_data(decided_a_data);
    //     */
    //     && sdba in db2
    // }

    predicate pred_4_1_g_ii(dvn: DVState)    
    {
        forall hn, s1: nat, s2: nat, vp, db2 |
            && hn in dvn.honest_nodes_states.Keys
            && var hn_state := dvn.honest_nodes_states[hn];
            && s2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys            
            && s1 < s2
            && hn in dvn.consensus_on_attestation_data[s1].honest_nodes_validity_functions.Keys
            && hn in dvn.consensus_on_attestation_data[s2].honest_nodes_validity_functions.Keys
            && vp in dvn.consensus_on_attestation_data[s2].honest_nodes_validity_functions[hn]        
            && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys   
            && db2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp]          
            && dvn.consensus_on_attestation_data[s1].decided_value.isPresent()
            ::                
            && var hn_state := dvn.honest_nodes_states[hn];
            && dvn.consensus_on_attestation_data[s1].decided_value.isPresent()
            && var decided_a_data := dvn.consensus_on_attestation_data[s1].decided_value.safe_get();
            && var sdba := construct_SlashingDBAttestation_from_att_data(decided_a_data);
            && sdba in db2
    }    

    predicate pred_4_1_g_iii(dvn: DVState)    
    {
        forall hn, s1: nat, s2: nat, vp, db2 |
            && hn in dvn.honest_nodes_states.Keys
            && var hn_state := dvn.honest_nodes_states[hn];
            && s1 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
            && s2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys            
            && s1 < s2       
            && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys  
            && db2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp]           
            ::                
            && var hn_state := dvn.honest_nodes_states[hn];
            && dvn.consensus_on_attestation_data[s1].decided_value.isPresent()
            && var decided_a_data := dvn.consensus_on_attestation_data[s1].decided_value.safe_get();
            && var sdba := construct_SlashingDBAttestation_from_att_data(decided_a_data);
            && sdba in db2
    }   

    predicate inv_g_iii_body_body(
        dvn: DVState, 
        hn_state: DVCNodeState
    ) 
    {
        forall s1: nat, s2: nat, vp, db2 |
            && s1 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
            && s2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys            
            && s1 < s2       
            && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys   
            && db2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp]           
            ::                
            && dvn.consensus_on_attestation_data[s1].decided_value.isPresent()
            && var decided_a_data := dvn.consensus_on_attestation_data[s1].decided_value.safe_get();
            && var sdba := construct_SlashingDBAttestation_from_att_data(decided_a_data);
            && sdba in db2        
    }

    predicate inv_g_iii_a_body_body(
        dvn: DVState, 
        n: BLSPubkey,
        n_state: DVCNodeState,
        index_next_attestation_duty_to_be_served: nat
    )
    {
        forall slot  |
            && slot in n_state.attestation_consensus_engine_state.att_slashing_db_hist
            ::
            exists i: nat :: 
                && i < index_next_attestation_duty_to_be_served
                && var an := dvn.sequence_attestation_duties_to_be_served[i];
                && an.attestation_duty.slot == slot 
                && an.node == n
    }          


    predicate inv_g_a(dvn: DVState)
    {
        forall n | n in dvn.honest_nodes_states.Keys :: inv_g_a_body(dvn, n)
    }

    predicate inv_g_a_body(
        dvn: DVState, 
        n: BLSPubkey
    )
    requires n in dvn.honest_nodes_states.Keys 
    {
        var n_state := dvn.honest_nodes_states[n];
        inv_g_a_body_body(dvn, n, n_state)
    }

    predicate inv_g_a_body_body(
        dvn: DVState, 
        n: BLSPubkey,
        n_state: DVCNodeState
    )
    {
        n_state.latest_attestation_duty.isPresent() ==>
            forall an |
                && an in dvn.sequence_attestation_duties_to_be_served.Values 
                && an.node == n 
                && an.attestation_duty.slot < n_state.latest_attestation_duty.safe_get().slot
            ::
                var slot := an.attestation_duty.slot;
                && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                // && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in n_state.attestation_slashing_db
    }    

    predicate inv_g_b_body_body(
        dvn: DVState, 
        n: BLSPubkey,
        n_state: DVCNodeState
    )
    {
        n_state.latest_attestation_duty.isPresent() ==>
            forall an |
                && an in dvn.sequence_attestation_duties_to_be_served.Values 
                && an.node == n 
                && an.attestation_duty.slot < n_state.latest_attestation_duty.safe_get().slot
            ::
                var slot := an.attestation_duty.slot;
                && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in n_state.attestation_slashing_db
    }        

    predicate inv_g_a_ii_body_body(
        dvn: DVState, 
        n: BLSPubkey,
        n_state: DVCNodeState
    )
    {
        (
            &&  |n_state.attestation_duties_queue| > 0 
            &&   !n_state.current_attestation_duty.isPresent()
        )
        ==>
            forall an |
                && an in dvn.sequence_attestation_duties_to_be_served.Values 
                && an.node == n 
                && an.attestation_duty.slot < n_state.attestation_duties_queue[0].slot
            ::
                var slot := an.attestation_duty.slot;
                && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
                // && construct_SlashingDBAttestation_from_att_data(dvn.consensus_on_attestation_data[slot].decided_value.safe_get()) in n_state.attestation_slashing_db
    }      

    predicate inv_g_a_iii_body_body(
        dvn: DVState, 
        n: BLSPubkey,
        n_state: DVCNodeState,
        index_next_attestation_duty_to_be_served: nat
    )
    {
        (
            &&  |n_state.attestation_duties_queue| == 0 
            &&   !n_state.current_attestation_duty.isPresent()
        ) ==>
            forall i:nat  |
                && i < index_next_attestation_duty_to_be_served
                && var an := dvn.sequence_attestation_duties_to_be_served[i];
                && an.node == n 
                ::
                && var an := dvn.sequence_attestation_duties_to_be_served[i];
                var slot := an.attestation_duty.slot;
                && dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
    }            



    predicate inv_g_c(dvn: DVState)
    {
        forall n | n in dvn.honest_nodes_states.Keys :: inv_g_c_body(dvn, n)
    }    

    predicate inv_g_c_body(
        dvn: DVState, 
        n: BLSPubkey
    )
    requires n in dvn.honest_nodes_states.Keys 
    {
        var n_state := dvn.honest_nodes_states[n];
        inv_g_c_body_body(dvn, n, n_state, dvn.index_next_attestation_duty_to_be_served)
    }

    predicate inv_g_c_body_body(
        dvn: DVState, 
        n: BLSPubkey,
        n_state: DVCNodeState,
        index_next_attestation_duty_to_be_served: nat
    )
    {
        n_state.latest_attestation_duty.isPresent() ==>
            forall i:nat  |
                && i < index_next_attestation_duty_to_be_served
                && var an := dvn.sequence_attestation_duties_to_be_served[i];
                && an in dvn.sequence_attestation_duties_to_be_served.Values 
                && an.node == n 
                && an.attestation_duty.slot > n_state.latest_attestation_duty.safe_get().slot 
                && !dvn.consensus_on_attestation_data[an.attestation_duty.slot].decided_value.isPresent()
                ::
                && var an := dvn.sequence_attestation_duties_to_be_served[i];
                an.attestation_duty in n_state.attestation_duties_queue
    }    

    predicate inv_g_c_ii_body_body(
        dvn: DVState, 
        n: BLSPubkey,
        n_state: DVCNodeState,
        index_next_attestation_duty_to_be_served: nat
    )
    {
        !n_state.latest_attestation_duty.isPresent() ==>
            forall i:nat  |
                && i < index_next_attestation_duty_to_be_served
                && var an := dvn.sequence_attestation_duties_to_be_served[i];
                && an in dvn.sequence_attestation_duties_to_be_served.Values 
                && an.node == n 
                && !dvn.consensus_on_attestation_data[an.attestation_duty.slot].decided_value.isPresent()
                ::
                && var an := dvn.sequence_attestation_duties_to_be_served[i];
                an.attestation_duty in n_state.attestation_duties_queue
    }    


    predicate inv_g_d_body_body(
        dvn: DVState, 
        n: BLSPubkey,
        n_state: DVCNodeState
    )
    {
        forall slot |
            && slot in n_state.future_att_consensus_instances_already_decided
            ::
            dvn.consensus_on_attestation_data[slot].decided_value.isPresent()
    }    


    /*
    predicate pred_4_1_g_b_thanh_hai(dvn: DVState)
    {
        forall hn, s1: nat, s2: nat, vp |
            && hn in dvn.honest_nodes_states.Keys
            && var hn_state := dvn.honest_nodes_states[hn];
            && s2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys            
            && s1 < s2
            && hn in dvn.consensus_on_attestation_data[s1].honest_nodes_validity_functions.Keys
            && hn in dvn.consensus_on_attestation_data[s2].honest_nodes_validity_functions.Keys
            // Another invariant to prove the two following lines
            && vp in dvn.consensus_on_attestation_data[s2].honest_nodes_validity_functions[hn]        
            && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys                        
            ::                
            && var hn_state := dvn.honest_nodes_states[hn];            
            && exists duty2: AttestationDuty :: 
                    && duty2 in hn_state.all_rcvd_duties && duty2.slot == s2
                    && var db2 := hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp];
                    && vp == (ad: AttestationData) => consensus_is_valid_attestation_data(db2, ad, duty2)            
                    && dvn.consensus_on_attestation_data[s1].decided_value.isPresent()
                    && var decided_a_data := dvn.consensus_on_attestation_data[s1].decided_value.safe_get();
                    && var sdba := construct_SlashingDBAttestation_from_att_data(decided_a_data);
                    /*
                    && var sdba := SlashingDBAttestation(
                                            source_epoch := decided_a_data.source.epoch,
                                            target_epoch := decided_a_data.target.epoch,
                                            signing_root := Some(hash_tree_root(decided_a_data)));
                    */                                            
                    && sdba in db2
    }    
    */

    predicate inv47_body(dvn: DVState, hn: BLSPubkey, s: Slot)
    {
        && is_honest_node(dvn, hn)
        && var hn_state := dvn.honest_nodes_states[hn];
        && ( s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                    ==> (exists duty: AttestationDuty :: duty in hn_state.all_rcvd_duties && duty.slot == s)
           )
    }

    predicate inv47(dvn: DVState)
    {
        forall hn: BLSPubkey, s: Slot | is_honest_node(dvn, hn) ::
            inv47_body(dvn, hn, s)
    }  

    predicate inv43_body_a(dvn: DVState, hn: BLSPubkey, s: Slot)
    requires is_honest_node(dvn, hn)
    requires s in dvn.consensus_on_attestation_data.Keys         
    requires hn in dvn.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys      
    requires && inv47_body(dvn, hn, s) 
             && inv46_a(dvn) 
    // requires && var hn_state := dvn.honest_nodes_states[hn];
    //          && exists duty: AttestationDuty :: duty in hn_state.all_rcvd_duties && duty.slot == s    
    {    
        && var hn_state := dvn.honest_nodes_states[hn];        
        && var duty: AttestationDuty :| duty in hn_state.all_rcvd_duties && duty.slot == s;        
        && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys                
        && (forall vp, db |
                && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s].Keys 
                && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
                ::
                && db <= hn_state.attestation_slashing_db                    
           )        
    }

    predicate inv43_body_b(dvn: DVState, hn: BLSPubkey, s: Slot, 
                            ci: ConsensusInstance<AttestationData>, h_nodes: set<BLSPubkey>)
    requires is_honest_node(dvn, hn)
    requires s in dvn.consensus_on_attestation_data.Keys         
    requires hn in dvn.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys      
    // requires && var hn_state := dvn.honest_nodes_states[hn];
    //         && exists duty: AttestationDuty :: duty in hn_state.all_rcvd_duties && duty.slot == s
    requires && inv47_body(dvn, hn, s) 
             && inv46_a(dvn)     
    requires s in dvn.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys                
    requires is_a_valid_decided_value_according_to_set_of_nodes(ci, h_nodes)
    {
        && var hn_state := dvn.honest_nodes_states[hn];        
        && var duty: AttestationDuty :| duty in hn_state.all_rcvd_duties && duty.slot == s;        
        && ( && dvn.consensus_on_attestation_data[s].decided_value.isPresent()
             && hn in h_nodes
                    ==> && var ad := dvn.consensus_on_attestation_data[s].decided_value.safe_get();
                        && exists vp, db :: 
                                        && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s].Keys 
                                        && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
                                        && consensus_is_valid_attestation_data(db, ad, duty)    
           )
    }

    predicate inv43(dvn: DVState)
    {
        forall hn: BLSPubkey, s: Slot |            
            && is_honest_node(dvn, hn)
            && var hn_state := dvn.honest_nodes_states[hn];
            && s in dvn.consensus_on_attestation_data.Keys
            && hn in dvn.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys      
            // && exists duty: AttestationDuty :: duty in hn_state.all_rcvd_duties && duty.slot == s            
            && inv47_body(dvn, hn, s) 
            && inv46_a(dvn)           
            ::            
            && inv43_body_a(dvn, hn, s)
            && ( dvn.consensus_on_attestation_data[s].decided_value.isPresent() 
                    ==> exists h_nodes :: && is_a_valid_decided_value_according_to_set_of_nodes(
                                                dvn.consensus_on_attestation_data[s], 
                                                h_nodes) 
                                          && inv43_body_b(dvn, hn, s, dvn.consensus_on_attestation_data[s], h_nodes)
               )                          
    }   

    predicate has_all_slashing_db_attestations_before_slot_s(
        db: set<SlashingDBAttestation>,
        S: set<SlashingDBAttestation>,
        s: Slot
    )
    requires (forall r: SlashingDBAttestation :: 
                    r in db ==> (exists data: AttestationData :: r.signing_root == Some(hash_tree_root(data))))
    {
        && S <= db
        && forall r | r in db && r !in S :: get_slot_from_slashing_db_attestation(r) >= s
        && forall r | r in S :: get_slot_from_slashing_db_attestation(r) < s
    }

    predicate inv44_body(dvn: DVState, hn: BLSPubkey, s1: Slot, s2: Slot, vp1: AttestationData -> bool, vp2: AttestationData -> bool, db2: set<SlashingDBAttestation>)
    requires is_honest_node(dvn, hn)
    requires && var hn_state: DVCNodeState := dvn.honest_nodes_states[hn];
             && s1 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
             && s2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
             && s1 < s2
             && vp1 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s1].Keys
             && vp2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys
    requires && var hn_state: DVCNodeState := dvn.honest_nodes_states[hn];
            && ( forall db, r: SlashingDBAttestation |
                    && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s1][vp1]
                    && r in db
                    :: 
                        (exists data: AttestationData :: r.signing_root == Some(hash_tree_root(data))) )
    {
        forall T |
        && var hn_state: DVCNodeState := dvn.honest_nodes_states[hn];
        && T in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s1][vp1]
        ::
        && var db1: set<SlashingDBAttestation> :| has_all_slashing_db_attestations_before_slot_s(T, db1, s2);
        && db1 <= db2   
    }
    predicate inv44(dvn: DVState)
    {
        forall hn: BLSPubkey | is_honest_node(dvn, hn) ::
            && var hn_state := dvn.honest_nodes_states[hn];
            && forall s1: Slot, s2: Slot, vp1, vp2, db2 |
                    && s1 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                    && s2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys 
                    && s1 < s2
                    && vp1 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s1].Keys
                    && vp2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2].Keys
                    && db2 in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s2][vp2]
                    && ( forall db, r: SlashingDBAttestation |
                            && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s1][vp1]
                            && r in db
                            :: 
                                (exists data: AttestationData :: r.signing_root == Some(hash_tree_root(data))) )
                    ::
                    inv44_body(dvn, hn, s1, s2, vp1, vp2, db2)
                    
    }  


    predicate inv45(dvn: DVState)
    {
        forall hn: BLSPubkey | is_honest_node(dvn, hn) ::
            && var hn_state := dvn.honest_nodes_states[hn];
            && forall s: Slot, vp, db | 
                && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
                && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s]
                && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
                ::
                    db <= hn_state.attestation_slashing_db
    }  

    predicate inv46_a(dvn: DVState)
    {
        forall hn: BLSPubkey, s: Slot | is_honest_node(dvn, hn) ::
            && var hn_state := dvn.honest_nodes_states[hn];
            && ( hn in dvn.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
                    ==> s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys)
    }

    predicate inv46_b_body(dvn: DVState, hn: BLSPubkey, s: Slot, vp: AttestationData -> bool)
    requires is_honest_node(dvn, hn) 
    requires hn in dvn.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
    requires s in dvn.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys
    {
        && var hn_state := dvn.honest_nodes_states[hn];
        && ( vp in dvn.consensus_on_attestation_data[s].honest_nodes_validity_functions[hn]
                ==> vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s] )
    }
    
    predicate inv46_b(dvn: DVState)
    {
        forall hn: BLSPubkey, s: Slot ::
            && is_honest_node(dvn, hn) 
            && var hn_state := dvn.honest_nodes_states[hn];
            && hn in dvn.consensus_on_attestation_data[s].honest_nodes_validity_functions.Keys
            && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
            ==> ( forall vp: AttestationData -> bool ::
                    inv46_b_body(dvn, hn, s, vp)
                )                    
    }  
    
    

    predicate safety(dvn: DVState)
    {
        forall a: Attestation ::
            a in dvn.globally_signed_attestations 
                ==> 
                (
                    && var S := dvn.globally_signed_attestations - { a };
                    && !is_slashable_attestation_data_in_set_of_attestations(S, a.data)
                )
    }

    // For every consensus instance ci, ci.decided value.isP resent() 
    // if and only if is a valid decided value(ci).
    predicate inv41<D(!new, 0)>(ci: ConsensusInstance<D>)
    {
        ci.decided_value.isPresent()
            <==> is_a_valid_decided_value(ci)            
    }

    predicate honest_nodes_with_validityPredicate(consa: ConsensusInstance<AttestationData>,  h_nodes_a: set<BLSPubkey>)
    requires h_nodes_a <= consa.honest_nodes_validity_functions.Keys  
    requires |h_nodes_a| >= quorum(|consa.all_nodes|) 
                                        - (|consa.all_nodes| - |consa.honest_nodes_status.Keys|)
    requires consa.decided_value.isPresent()
    {
        forall n | n in h_nodes_a 
            :: exists vp: AttestationData -> bool | vp in consa.honest_nodes_validity_functions[n] 
                    :: vp(consa.decided_value.safe_get())
    }
    
    


    

    predicate pred_4_1_witness(
        dvn: DVState, a: Attestation, a': Attestation, m: BLSPubkey,
        consa: ConsensusInstance<AttestationData>, consa': ConsensusInstance<AttestationData>,
        h_nodes_a: set<BLSPubkey>, h_nodes_a': set<BLSPubkey>)
    {
        && is_honest_node(dvn, m)                
        && consa == dvn.consensus_on_attestation_data[a.data.slot]
        && consa' == dvn.consensus_on_attestation_data[a'.data.slot]
        && m in consa.honest_nodes_validity_functions.Keys
        && m in h_nodes_a
        && m in consa'.honest_nodes_validity_functions.Keys                
        && m in h_nodes_a'
        && consa'.honest_nodes_validity_functions[m] != {}
        && is_a_valid_decided_value_according_to_set_of_nodes(consa, h_nodes_a) 
        && is_a_valid_decided_value_according_to_set_of_nodes(consa', h_nodes_a') 
    }


    predicate inv49(dvn: DVState)
    {
        forall hn: BLSPubkey, d1: AttestationDuty, d2: AttestationDuty | 
            && is_honest_node(dvn, hn)
            && var hn_state := dvn.honest_nodes_states[hn];
            && d1 in hn_state.all_rcvd_duties
            && d2 in hn_state.all_rcvd_duties
            && d1.slot == d2.slot
            ::
            d1 == d2
    }

    predicate inv50_body(dvn: DVState, hn: BLSPubkey, s: Slot, 
                            db: set<SlashingDBAttestation>, duty: AttestationDuty, vp: AttestationData -> bool)
    requires && is_honest_node(dvn, hn)
             && var hn_state := dvn.honest_nodes_states[hn];
             && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
             && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s]
             // && duty in hn_state.all_rcvd_duties
             // && duty.slot == s
    {
        && var hn_state := dvn.honest_nodes_states[hn];
        && duty.slot == s
        && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
        && vp == (ad: AttestationData) => consensus_is_valid_attestation_data(db, ad, duty)
    }
    predicate inv50(dvn: DVState)
    {
        forall hn: BLSPubkey, s: Slot, vp: AttestationData -> bool | 
            && is_honest_node(dvn, hn)
            && var hn_state := dvn.honest_nodes_states[hn];
            && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
            && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s]
            ::
            exists duty, db ::
                && var hn_state := dvn.honest_nodes_states[hn];
                && inv50_body(dvn, hn, s, db, duty, vp)
    }

    predicate inv51_body(hn_state: DVCNodeState, s: Slot)
    requires s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
    {
        exists duty: AttestationDuty :: 
                    && duty in hn_state.all_rcvd_duties
                    && duty.slot == s
    }


    predicate inv51(dvn: DVState)
    {
        forall hn: BLSPubkey, s: Slot ::
            && is_honest_node(dvn, hn) 
            && var hn_state := dvn.honest_nodes_states[hn];
            && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
            ==>
            inv51_body(hn_state, s)                
    }

    predicate inv48_body(dvn: DVState, s: Slot, hn: BLSPubkey) 
    {
        && var ci := dvn.consensus_on_attestation_data[s];
        && hn in ci.honest_nodes_validity_functions.Keys
        && ci.honest_nodes_validity_functions[hn] != {}                
    }
    
    predicate inv48(dvn: DVState)
    {
        forall s: Slot ::
            && var ci := dvn.consensus_on_attestation_data[s];
            && ( ci.decided_value.isPresent()
                    <==> ( exists h_nodes :: 
                                && is_a_valid_decided_value_according_to_set_of_nodes(ci, h_nodes)            
                                && ( forall hn: BLSPubkey :: 
                                            && is_honest_node(dvn, hn)
                                            && hn in h_nodes
                                                    ==> inv48_body(dvn, s, hn)                                        
                                   )
                         )
                              
               )
    }


    predicate inv53(dvn: DVState)
    {
        forall s: Slot ::
            && var ci := dvn.consensus_on_attestation_data[s];            
            && dvn.all_nodes == ci.all_nodes
            && dvn.honest_nodes_states.Keys == ci.honest_nodes_status.Keys
    }
    

    predicate inv1(dvn: DVState)
    {        
        && var all_nodes := dvn.all_nodes;
        && var honest_nodes := dvn.honest_nodes_states.Keys;
        && var dishonest_nodes := dvn.adversary.nodes;
        && 0 < |all_nodes|
        && quorum(|all_nodes|) <= |honest_nodes|
        && |dishonest_nodes| <= f(|all_nodes|) 
        && all_nodes == honest_nodes + dishonest_nodes
        && honest_nodes * dishonest_nodes == {}
    }

    predicate inv2(dvn: DVState)
    {
        forall ci | ci in dvn.consensus_on_attestation_data.Values
            :: && ci.all_nodes == dvn.all_nodes
               && ci.honest_nodes_status.Keys == dvn.honest_nodes_states.Keys  
               && ci.honest_nodes_status.Keys <= ci.all_nodes
               && ci.honest_nodes_validity_functions.Keys <= ci.honest_nodes_status.Keys
               && |ci.all_nodes - ci.honest_nodes_status.Keys| <= f(|ci.all_nodes|)
    }

    predicate inv3(dvn: DVState)
    {
        forall n | n in dvn.honest_nodes_states.Keys :: 
            var nodes := dvn.honest_nodes_states[n];
            && nodes.construct_signed_attestation_signature == dvn.construct_signed_attestation_signature
            && nodes.dv_pubkey == dvn.dv_pubkey       
            && nodes.peers == dvn.all_nodes
    }

    predicate inv4(dvn: DVState)
    {
        forall n: BLSPubkey | n in dvn.honest_nodes_states.Keys ::            
            && var nodes := dvn.honest_nodes_states[n];
            && forall duty: AttestationDuty | duty in nodes.all_rcvd_duties ::
                exists k: nat :: 
                    && k < dvn.index_next_attestation_duty_to_be_served
                    && dvn.sequence_attestation_duties_to_be_served[k].node == n
                    && dvn.sequence_attestation_duties_to_be_served[k].attestation_duty == duty
    }

    predicate inv5_body(dvc: DVCNodeState)
    {
        forall k: nat ::
            0 <= k < |dvc.attestation_duties_queue|
                ==> ( && var queued_duty: AttestationDuty := dvc.attestation_duties_queue[k];
                      && queued_duty in dvc.all_rcvd_duties )
    }

    predicate inv5(dvn: DVState)
    {
        forall hn: BLSPubkey | hn in dvn.honest_nodes_states.Keys ::            
            && var dvc := dvn.honest_nodes_states[hn];
            && inv5_body(dvc)
    }

    predicate inv6_body(dvc: DVCNodeState)
    {
        dvc.current_attestation_duty.isPresent()
            ==> dvc.current_attestation_duty.safe_get()
                    in dvc.all_rcvd_duties
    }

    predicate inv6(dvn: DVState)
    {
        forall hn: BLSPubkey | hn in dvn.honest_nodes_states.Keys ::            
            && var dvc := dvn.honest_nodes_states[hn];
            && inv6_body(dvc)
    }

    predicate inv7_body(dvc: DVCNodeState)
    {
        dvc.latest_attestation_duty.isPresent()
            ==> dvc.latest_attestation_duty.safe_get()
                    in dvc.all_rcvd_duties
    }

    predicate inv7(dvn: DVState)
    {
        forall hn: BLSPubkey | hn in dvn.honest_nodes_states.Keys ::            
            && var dvc := dvn.honest_nodes_states[hn];
            && inv7_body(dvc)
    }

    predicate inv8_body(dvc: DVCNodeState)
    {
        !dvc.latest_attestation_duty.isPresent()
            ==> !dvc.current_attestation_duty.isPresent()
    }

    predicate inv8(dvn: DVState)
    {
        forall hn: BLSPubkey | hn in dvn.honest_nodes_states.Keys ::            
            && var dvc := dvn.honest_nodes_states[hn];
            && inv8_body(dvc)
    }
  
    predicate inv9_body(dvc: DVCNodeState)
    {
        !dvc.latest_attestation_duty.isPresent()
            ==> ( || !dvc.current_attestation_duty.isPresent()
                  || ( && dvc.latest_attestation_duty.isPresent()
                       && dvc.current_attestation_duty.isPresent()
                       && dvc.current_attestation_duty.safe_get()
                                == dvc.latest_attestation_duty.safe_get()
                     )
                )
    }

    predicate inv9(dvn: DVState)
    {
        forall hn: BLSPubkey | hn in dvn.honest_nodes_states.Keys ::            
            && var dvc := dvn.honest_nodes_states[hn];
            && inv9_body(dvc)
    }

    predicate inv10_body(dvc: DVCNodeState)
    {
        dvc.current_attestation_duty.isPresent()
            ==> ( && dvc.latest_attestation_duty.isPresent()
                  && dvc.current_attestation_duty.safe_get()
                                == dvc.latest_attestation_duty.safe_get()                   
                )
    }

    predicate inv10(dvn: DVState)
    {
        forall hn: BLSPubkey | hn in dvn.honest_nodes_states.Keys ::            
            && var dvc := dvn.honest_nodes_states[hn];
            && inv10_body(dvc)
    }

    predicate inv11_body(dvc: DVCNodeState)
    {
        !dvc.latest_attestation_duty.isPresent()
            ==> |dvc.attestation_duties_queue| == 0
    }

    predicate inv11(dvn: DVState)
    {
        forall hn: BLSPubkey | hn in dvn.honest_nodes_states.Keys ::            
            && var dvc := dvn.honest_nodes_states[hn];
            && inv11_body(dvc)
    }

    predicate invNetwork(
        dvn: DVState
    )
    {
         forall m | 
                && m in dvn.att_network.messagesInTransit
            ::
                m.message in dvn.att_network.allMessagesSent       
    }

/*
    predicate inv3(dvn: DVState)
    {
        forall k1: nat, k2: nat :: 
            dvn.sequence_attestation_duties_to_be_served[k1].attestation_duty.slot 
                    == dvn.sequence_attestation_duties_to_be_served[k2].attestation_duty.slot  
            ==> 
            dvn.sequence_attestation_duties_to_be_served[k1].attestation_duty
                    == dvn.sequence_attestation_duties_to_be_served[k2].attestation_duty
    }

    predicate inv4(dvn: DVState)
    {
        forall k1: nat, k2: nat :: 
            && k1 < k2
            && dvn.sequence_attestation_duties_to_be_served[k1].node 
                    == dvn.sequence_attestation_duties_to_be_served[k2].node
            ==> 
            dvn.sequence_attestation_duties_to_be_served[k1].attestation_duty.slot 
                    < dvn.sequence_attestation_duties_to_be_served[k2].attestation_duty.slot  
    }
    */

    predicate inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent_single_node(
        dvn: DVState,
        n: BLSPubkey
    )
    requires n in dvn.honest_nodes_states.Keys 
    {
        dvn.honest_nodes_states[n].attestation_shares_to_broadcast.Values <= dvn.att_network.allMessagesSent
    }

    predicate inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent(
        dvn: DVState
    )
    {
        forall n |
            n in dvn.honest_nodes_states.Keys 
            ::
        inv_attestation_shares_to_broadcast_is_a_subset_of_all_messages_sent_single_node(dvn, n)
    }    
}