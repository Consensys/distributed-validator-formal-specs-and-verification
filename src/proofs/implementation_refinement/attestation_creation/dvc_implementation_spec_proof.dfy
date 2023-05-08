include "../../../common/commons.dfy"
include "../../../specs/dvc/dvc_attestation_creation.dfy"
include "../../no_slashable_attestations/common/att_dvc_spec_axioms.dfy"

module Att_DVC_Implementation_Proofs refines Att_DVC_Implementation
{
    import opened Att_DVC_Spec_NonInstr
    import opened Att_DVC_Externs = Att_DVC_Externs_Proofs
    import opened Att_DVC_Spec_Axioms

    function toAttestationConsensusValidityCheckState(
        acvc: ConsensusValidityCheck<AttestationData>
    ): AttestationConsensusValidityCheckState
    requires isAttestationConsensusValidityCheck(acvc)
    reads acvc, acvc.slashing_db
    {
        var attestation_duty := (acvc as AttestationConsensusValidityCheck).attestation_duty;
        var pubkey := (acvc as AttestationConsensusValidityCheck).dv_pubkey;
        var attestation_slashing_db := acvc.slashing_db.attestations[pubkey];
        AttestationConsensusValidityCheckState(
            attestation_duty := attestation_duty,
            validityPredicate := (ad: AttestationData) => ci_decision_is_valid_attestation_data(attestation_slashing_db, ad, attestation_duty)
        )
    }    

    predicate isAttestationConsensusValidityCheck(
        cvc: ConsensusValidityCheck<AttestationData>
    )
    reads cvc
    {
        cvc is AttestationConsensusValidityCheck
    }

    function toAttestationConsensusValidityCheck(
        cvc: ConsensusValidityCheck<AttestationData>
    ): AttestationConsensusValidityCheck
    requires isAttestationConsensusValidityCheck(cvc)
    reads cvc
    {
        cvc as AttestationConsensusValidityCheck
    }

    lemma lemmaMapKeysHasOneEntryInItems<K, V>(m: map<K, V>, k: K)  
    requires k in m.Keys
    ensures exists i :: i in m.Items && i.0 == k 
    {
        assert (k, m[k]) in m.Items;
    }
    
    function get_active_attestation_consensus_instances(
        m: map<Slot, ConsensusValidityCheck<AttestationData>>
    ): (r: map<Slot, AttestationConsensusValidityCheckState>)
    reads m.Values, set v: ConsensusValidityCheck<AttestationData>  | && v in m.Values  :: v.slashing_db
    ensures r.Keys <= m.Keys
    ensures forall k | k in r.Keys :: isAttestationConsensusValidityCheck(m[k]) && r[k] == toAttestationConsensusValidityCheckState(m[k])
    {  
            map it | 
                        && it in m.Items 
                        && isAttestationConsensusValidityCheck(it.1)
                    :: 
                    it.0 := toAttestationConsensusValidityCheckState(it.1)           
    }

    function toConsensusEngineState(ce: Consensus<AttestationData>): (r: ConsensusEngineState)
    reads ce, ce.consensus_instances_started.Values, set v: ConsensusValidityCheck<AttestationData>  | && v in ce.consensus_instances_started.Values  :: v.slashing_db
    {
        ConsensusEngineState(
            active_attestation_consensus_instances := get_active_attestation_consensus_instances(ce.consensus_instances_started)   
        )
    }

    twostate predicate lemmaConsensusInstancesHaveBeenRemovedPrecond(
        ce: Consensus<AttestationData>,
        removed_keys: set<Slot>
    )
    reads ce, ce.consensus_instances_started.Values, set v: ConsensusValidityCheck<AttestationData>  | && v in ce.consensus_instances_started.Values  :: v.slashing_db
    {
        ce.consensus_instances_started == old(ce.consensus_instances_started) - removed_keys 
        && forall v | v in ce.consensus_instances_started.Values :: 
            && old(allocated(v))
            && unchanged(v.slashing_db)
            && unchanged(v)   
    }    

    twostate lemma lemmaConsensusInstancesHaveBeenRemoved(
        ce: Consensus<AttestationData>,
        removed_keys: set<Slot>
    )
    requires lemmaConsensusInstancesHaveBeenRemovedPrecond(ce, removed_keys)
    ensures toConsensusEngineState(ce) == old(toConsensusEngineState(ce)).(
        active_attestation_consensus_instances := old(toConsensusEngineState(ce)).active_attestation_consensus_instances - removed_keys
    )
    {      
    }    

    twostate predicate lemmaConsensusInstancesAreTheSamePrecond(
        ce: Consensus<AttestationData>
    )
    reads ce, ce.consensus_instances_started.Values, set v: ConsensusValidityCheck<AttestationData>  | && v in ce.consensus_instances_started.Values  :: v.slashing_db
    {
        && unchanged(ce)
        && forall v | v in ce.consensus_instances_started.Values :: 
            && old(allocated(v))
            && isAttestationConsensusValidityCheck(v) 
            && unchanged(v.slashing_db) 
            && unchanged(v)   
    }

    twostate lemma lemmaConsensusInstancesAreTheSame(
        ce: Consensus<AttestationData>
    )
    requires lemmaConsensusInstancesAreTheSamePrecond(ce)
    ensures old(toConsensusEngineState(ce)) == toConsensusEngineState(ce)
    {

        forall e | e in old(toConsensusEngineState(ce)).active_attestation_consensus_instances.Keys
        ensures e in toConsensusEngineState(ce).active_attestation_consensus_instances.Keys;
        {
            lemmaMapKeysHasOneEntryInItems(old(toConsensusEngineState(ce)).active_attestation_consensus_instances, e);
        } 

        assert old(toConsensusEngineState(ce)).active_attestation_consensus_instances.Keys == toConsensusEngineState(ce).active_attestation_consensus_instances.Keys;        
    }

    export PublicInterface...
        reveals *

    function seqMinusToSet<T>(s1: seq<T>, s2: seq<T>): set<T>
    {
        if |s2| <= |s1| then
            var seqDiff := s1[|s2|..];
            assert s2 <= s1 ==> s2 + seqDiff == s1;
            seqToSet(seqDiff)
        else
            {}
    }

    class Att_DVC...
    {
        function toAtt_DVCState(): Att_DVCState
        reads this, bn, rs, att_consensus, slashing_db, att_consensus.consensus_instances_started.Values, set v: ConsensusValidityCheck<AttestationData>  | && v in att_consensus.consensus_instances_started.Values  :: v.slashing_db
        {
            Att_DVCState(
                current_attestation_duty := current_attestation_duty,
                latest_attestation_duty := latest_attestation_duty,
                attestation_duties_queue := attestation_duties_queue,
                attestation_slashing_db := slashing_db.attestations[dv_pubkey],
                rcvd_attestation_shares := rcvd_attestation_shares,
                attestation_shares_to_broadcast := attestation_shares_to_broadcast,
                attestation_consensus_engine_state := toConsensusEngineState(att_consensus),
                peers := peers,
                construct_signed_attestation_signature := construct_signed_attestation_signature,
                dv_pubkey := dv_pubkey,
                future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                bn := toBNState(bn),
                rs := toRSState(rs)
            )
        }  

        twostate function getOutputs(): (o: Outputs)
        reads this, network, bn
        {
            Outputs(
                att_shares_sent :=  setUnion(seqMinusToSet(network.att_shares_sent, old(network.att_shares_sent))),
                attestations_submitted := seqMinusToSet(bn.attestations_submitted, old(bn.attestations_submitted))
            )
        }              

        twostate function toAtt_DVCStateAndOuputs(): Att_DVCStateAndOuputs
        reads this, network, att_consensus, bn, rs, slashing_db, att_consensus.consensus_instances_started.Values, set v: ConsensusValidityCheck<AttestationData>  | && v in att_consensus.consensus_instances_started.Values :: v.slashing_db
        {
            Att_DVCStateAndOuputs(
                state := toAtt_DVCState(),
                outputs := getOutputs()
            )
        }        

        predicate isValidReprExtended()
        reads *
        {
            && (forall vp | vp in att_consensus.consensus_instances_started.Values :: 
                        && isAttestationConsensusValidityCheck(vp)
                        && vp.slashing_db == this.slashing_db
                        && toAttestationConsensusValidityCheck(vp).dv_pubkey == this.dv_pubkey
            )
            && ValidRepr()
        }

        constructor...
        ensures 
                && isValidReprExtended()
                && Init(toAtt_DVCState(), dv_pubkey, peers, construct_signed_attestation_signature, initial_slashing_db.attestations[dv_pubkey], rs.pubkey)
        {
            ...;
        }

        method process_event...
        ensures (old(isValidReprExtended()) && f_process_event.requires(old(toAtt_DVCState()), event)) ==>    
                && isValidReprExtended()
                && f_process_event(old(toAtt_DVCState()), event) == toAtt_DVCStateAndOuputs()
                && s.Success?        
        {
            ...; 

            {
                if event.ServeAttestationDuty?
                {    
                    assert (old(isValidReprExtended()) && f_process_event.requires(old(toAtt_DVCState()), event)) ==> 
                        && f_process_event(old(toAtt_DVCState()), event) == toAtt_DVCStateAndOuputs()
                        && isValidReprExtended();
                }
                else if event.AttConsensusDecided?
                {
                    assert (old(isValidReprExtended()) && f_process_event.requires(old(toAtt_DVCState()), event)) ==> 
                        && f_process_event(old(toAtt_DVCState()), event) == toAtt_DVCStateAndOuputs()
                        && isValidReprExtended();       
                }         
                else if event.ReceivedAttestationShare?
                {    
                    assert (old(isValidReprExtended()) && f_process_event.requires(old(toAtt_DVCState()), event)) ==> 
                        && f_process_event(old(toAtt_DVCState()), event) == toAtt_DVCStateAndOuputs()
                        && isValidReprExtended();  
                }              
                else if event.ImportedNewBlock? 
                {    assert (old(isValidReprExtended()) && f_process_event.requires(old(toAtt_DVCState()), event)) ==> 
                        && f_process_event(old(toAtt_DVCState()), event) == toAtt_DVCStateAndOuputs()
                        && isValidReprExtended();  
                }              
                else if event.ResendAttestationShares?
                {    
                    assert (old(isValidReprExtended()) && f_process_event.requires(old(toAtt_DVCState()), event)) ==> 
                        && f_process_event(old(toAtt_DVCState()), event) == toAtt_DVCStateAndOuputs()
                        && isValidReprExtended(); 
                }               
                else
                {    
                    assert (old(isValidReprExtended()) && f_process_event.requires(old(toAtt_DVCState()), event)) ==> 
                        && f_process_event(old(toAtt_DVCState()), event) == toAtt_DVCStateAndOuputs()
                        && isValidReprExtended(); 
                }                   
                ...;
            }   
        }

        method serve_attestation_duty...
        ensures (old(isValidReprExtended()) && f_serve_attestation_duty.requires(old(toAtt_DVCState()), attestation_duty)) ==> 
                && f_serve_attestation_duty(old(toAtt_DVCState()), attestation_duty) == toAtt_DVCStateAndOuputs()
                && isValidReprExtended()
                && s.Success?
                && unchanged(network)
                && unchanged(bn)
                && unchanged(rs)                
        {
            ...;
            {
                var o := toAtt_DVCState();
                ...;
                assert o == old(toAtt_DVCState()).(
                            attestation_duties_queue := old(toAtt_DVCState()).attestation_duties_queue + [attestation_duty]
                        );
                assert (old(isValidReprExtended()) && f_serve_attestation_duty.requires(old(toAtt_DVCState()), attestation_duty)) ==> f_serve_attestation_duty(old(toAtt_DVCState()), attestation_duty) == toAtt_DVCStateAndOuputs();
            }

        }

        function  f_check_for_next_duty_helper(process: Att_DVCState): Att_DVCState
        requires forall ad | ad in process.attestation_duties_queue :: ad.slot !in process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
        requires process.attestation_duties_queue != []
        requires process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided.Keys 
        
        {
            var queue_head := process.attestation_duties_queue[0];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, process.future_att_consensus_instances_already_decided[queue_head.slot]);
            process.(
                attestation_duties_queue := process.attestation_duties_queue[1..],
                future_att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided - {queue_head.slot},
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    process.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                        
            )
        }          

        method check_for_next_queued_duty...
        ensures (old(isValidReprExtended()) && f_check_for_next_duty.requires(old(toAtt_DVCState())))==> 
                && f_check_for_next_duty(old(toAtt_DVCState())) == toAtt_DVCStateAndOuputs()
                && isValidReprExtended()
                && s.Success?
                && unchanged(network)
                && unchanged(bn)
                && unchanged(rs)   
                && unchanged(`rcvd_attestation_shares)
                && unchanged(`attestation_shares_to_broadcast)
                && unchanged(`construct_signed_attestation_signature)
                && unchanged(`peers)
                && unchanged(`dv_pubkey)
                && fresh(att_consensus.Repr - old(att_consensus.Repr))                     

        {
            if...
            {
                if...
                {
                    ...;
                    {                      
                        if (old(isValidReprExtended()) && f_check_for_next_duty.requires(old(toAtt_DVCState()))) 
                        {
                            var rs := f_check_for_next_duty_helper(old(toAtt_DVCState()));                              

                            forall e | e in old(toAtt_DVCState()).attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
                            ensures e in rs.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
                            {
                                lemmaMapKeysHasOneEntryInItems(old(toAtt_DVCState()).attestation_consensus_engine_state.active_attestation_consensus_instances, e);
                            }   

                            lemmaAttestationHasBeenAddedToSlashingDb(old(future_att_consensus_instances_already_decided)[queue_head.slot], rs);                       
                                                    
                            assert f_check_for_next_duty_helper(old(toAtt_DVCState())) == toAtt_DVCState(); 

                        }
                       
                        ...;

                        assert (old(isValidReprExtended()) && f_check_for_next_duty.requires(old(toAtt_DVCState()))) ==> f_check_for_next_duty(old(toAtt_DVCState())) == toAtt_DVCStateAndOuputs();       
                    }

                }
                else if...
                {
                    ...;
                    assert (old(isValidReprExtended()) && f_check_for_next_duty.requires(old(toAtt_DVCState()))) ==> f_check_for_next_duty(old(toAtt_DVCState())) == toAtt_DVCStateAndOuputs();
                }
                else
                {
                    assert (old(isValidReprExtended()) && f_check_for_next_duty.requires(old(toAtt_DVCState()))) ==> f_check_for_next_duty(old(toAtt_DVCState())) == toAtt_DVCStateAndOuputs();
                }
            }
            else
            {
                assert (old(isValidReprExtended()) && f_check_for_next_duty.requires(old(toAtt_DVCState()))) ==> f_check_for_next_duty(old(toAtt_DVCState())) == toAtt_DVCStateAndOuputs();
            }
        }     

        method start_next_duty...
        ensures 
                old(isValidReprExtended()) ==>
                (
                    && isValidReprExtended()
                    && (f_start_next_duty.requires(old(toAtt_DVCState()), attestation_duty) ==> 
                        && (f_start_next_duty(old(toAtt_DVCState()), attestation_duty) == toAtt_DVCStateAndOuputs())
                        && s.Success?
                        && unchanged(network)
                        && unchanged(bn)
                        && unchanged(rs)
                        && current_attestation_duty == Some(attestation_duty)
                        && latest_attestation_duty == Some(attestation_duty)
                        && unchanged(`attestation_duties_queue)
                        && unchanged(slashing_db)
                        && unchanged(`rcvd_attestation_shares)
                        && unchanged(`attestation_shares_to_broadcast)
                        && unchanged(`construct_signed_attestation_signature)
                        && unchanged(`peers)
                        && unchanged(`dv_pubkey)
                        && unchanged(`future_att_consensus_instances_already_decided)
                        && att_consensus.consensus_instances_started.Keys == old(att_consensus.consensus_instances_started.Keys) + {attestation_duty.slot}
                        && fresh(att_consensus.Repr - old(att_consensus.Repr))
                    )
                )
        {
            if old(isValidReprExtended())
            {
                forall e | e in old(att_consensus.consensus_instances_started.Keys)
                ensures e in old(get_active_attestation_consensus_instances(att_consensus.consensus_instances_started)).Keys; // TOOD: Possible violation of postcondition
                {
                    lemmaMapKeysHasOneEntryInItems(old(att_consensus.consensus_instances_started), e);
                }     
            }                 
            ...;
            {
                ...;
            }
            if old(isValidReprExtended())
            {
                lemmaMapKeysHasOneEntryInItems(att_consensus.consensus_instances_started, attestation_duty.slot);
                                                                                     
                assert f_start_next_duty(old(toAtt_DVCState()), attestation_duty) == toAtt_DVCStateAndOuputs();
            }
        }

        method update_attestation_slashing_db...
        ensures f_update_attestation_slashing_db(old(toAtt_DVCState()).attestation_slashing_db, attestation_data) == this.slashing_db.attestations[this.dv_pubkey] == toAtt_DVCState().attestation_slashing_db
        ensures  var slashing_db_attestation := SlashingDBAttestation(
                                                source_epoch := attestation_data.source.epoch,
                                                target_epoch := attestation_data.target.epoch,
                                                signing_root := Some(hash_tree_root(attestation_data)));
            slashing_db.attestations == old(slashing_db.attestations)[dv_pubkey := old(slashing_db.attestations)[dv_pubkey] + {slashing_db_attestation}]
        ensures && unchanged(slashing_db`proposals)
                && unchanged(this)
                && unchanged(network)
                && unchanged(rs)
                && unchanged(bn)
                && unchanged(att_consensus)
                && unchanged(att_consensus.consensus_instances_started.Values)
        {
            ...;
        }
        
        

        function f_att_consensus_decided_helper(
            process: Att_DVCState,
            id: Slot,
            decided_attestation_data: AttestationData
        ): Att_DVCStateAndOuputs
        requires process.current_attestation_duty.isPresent()
        requires forall ad | ad in process.attestation_duties_queue :: ad.slot !in process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys    
        {
            var local_current_attestation_duty := process.current_attestation_duty.safe_get();
            var attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);

            var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
            var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
            var attestation_signature_share := rs_sign_attestation(decided_attestation_data, fork_version, attestation_signing_root, process.rs);
            var attestation_with_signature_share := AttestationShare(
                    aggregation_bits := get_aggregation_bits(local_current_attestation_duty.validator_index),
                    data := decided_attestation_data, 
                    signature := attestation_signature_share
                ); 

            var newProcess := 
                process.(
                    current_attestation_duty := None,
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                    attestation_slashing_db := attestation_slashing_db,
                    attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                        process.attestation_consensus_engine_state,
                        attestation_slashing_db
                    )
                )
                ;

            Att_DVCStateAndOuputs(
                newProcess,
                outputs := getEmptyOuputs().(
                    att_shares_sent := multicast(attestation_with_signature_share, process.peers)
                )                  
            )                
        }  

        twostate lemma lemmaAttestationHasBeenAddedToSlashingDbForall(
            attestation_data: AttestationData
        )
        requires old(isValidReprExtended())
        requires isValidReprExtended()
        requires unchanged(att_consensus)
        requires var slashing_db_attestation := SlashingDBAttestation(
                                                source_epoch := attestation_data.source.epoch,
                                                target_epoch := attestation_data.target.epoch,
                                                signing_root := Some(hash_tree_root(attestation_data)));        
                && slashing_db.attestations == old(slashing_db.attestations)[dv_pubkey := old(slashing_db.attestations)[dv_pubkey] + {slashing_db_attestation}]
        ensures
                forall p: Att_DVCState |
                        && p.dv_pubkey == dv_pubkey  
                        && var new_attestation_slashing_db := f_update_attestation_slashing_db(old(toAtt_DVCState()).attestation_slashing_db, attestation_data);
                        && p.attestation_slashing_db == f_update_attestation_slashing_db(old(toAtt_DVCState()).attestation_slashing_db, attestation_data)
                        && p.attestation_consensus_engine_state == updateConsensusInstanceValidityCheck(
                            old(toAtt_DVCState()).attestation_consensus_engine_state,
                            new_attestation_slashing_db
                        )
                    ::  
                        p.attestation_consensus_engine_state ==  toAtt_DVCState().attestation_consensus_engine_state
        {
            forall p: Att_DVCState |
                && p.dv_pubkey == dv_pubkey  
                && var new_attestation_slashing_db := f_update_attestation_slashing_db(old(toAtt_DVCState()).attestation_slashing_db, attestation_data);
                && p.attestation_slashing_db == f_update_attestation_slashing_db(old(toAtt_DVCState()).attestation_slashing_db, attestation_data)
                && p.attestation_consensus_engine_state == updateConsensusInstanceValidityCheck(
                    old(toAtt_DVCState()).attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )
            ensures  p.attestation_consensus_engine_state ==  toAtt_DVCState().attestation_consensus_engine_state
            {
                forall e | e in old(toAtt_DVCState()).attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
                ensures e in p.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
                {
                    lemmaMapKeysHasOneEntryInItems(old(toAtt_DVCState()).attestation_consensus_engine_state.active_attestation_consensus_instances, e);
                } 
            }                  
        }

        twostate lemma lemmaAttestationHasBeenAddedToSlashingDb(
            attestation_data: AttestationData,
            p: Att_DVCState
        )
        requires old(isValidReprExtended())
        requires isValidReprExtended()
        requires unchanged(att_consensus)
        requires var slashing_db_attestation := SlashingDBAttestation(
                                                source_epoch := attestation_data.source.epoch,
                                                target_epoch := attestation_data.target.epoch,
                                                signing_root := Some(hash_tree_root(attestation_data)));        
                && slashing_db.attestations == old(slashing_db.attestations)[dv_pubkey := old(slashing_db.attestations)[dv_pubkey] + {slashing_db_attestation}]
        requires

                        && p.dv_pubkey == dv_pubkey  
                        && var new_attestation_slashing_db := f_update_attestation_slashing_db(old(toAtt_DVCState()).attestation_slashing_db, attestation_data);
                        && p.attestation_slashing_db == f_update_attestation_slashing_db(old(toAtt_DVCState()).attestation_slashing_db, attestation_data)
                        && p.attestation_consensus_engine_state == updateConsensusInstanceValidityCheck(
                            old(toAtt_DVCState()).attestation_consensus_engine_state,
                            new_attestation_slashing_db
                        )
        ensures
                        p.attestation_consensus_engine_state ==  toAtt_DVCState().attestation_consensus_engine_state
        {
            forall e | e in old(toAtt_DVCState()).attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
            ensures e in p.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
            {
                lemmaMapKeysHasOneEntryInItems(old(toAtt_DVCState()).attestation_consensus_engine_state.active_attestation_consensus_instances, e);
            }           
        }                        

        method att_consensus_decided...
        ensures (old(isValidReprExtended()) && f_att_consensus_decided.requires(old(toAtt_DVCState()), id, decided_attestation_data)) ==> 
                && f_att_consensus_decided(old(toAtt_DVCState()), id, decided_attestation_data) == toAtt_DVCStateAndOuputs()
                && isValidReprExtended()
                && r.Success?
        {
            if...
            {
                ...;
                {
                    if old(isValidReprExtended()) && f_att_consensus_decided.requires(old(toAtt_DVCState()), id, decided_attestation_data)
                    {
                        var r := f_att_consensus_decided_helper(old(toAtt_DVCState()), id, decided_attestation_data);
                        var s := old(current_attestation_duty).safe_get().slot;
                        var rs := r.state;

                        lemmaAttestationHasBeenAddedToSlashingDb(decided_attestation_data, rs); 

                        assert f_att_consensus_decided_helper(old(toAtt_DVCState()), id, decided_attestation_data).state == toAtt_DVCStateAndOuputs().state; 
                    }                
                    ...;
                }
            }
            else 
            {
                assert (old(isValidReprExtended()) && f_att_consensus_decided.requires(old(toAtt_DVCState()), id, decided_attestation_data)) ==>
                    f_att_consensus_decided(old(toAtt_DVCState()), id, decided_attestation_data) == toAtt_DVCStateAndOuputs();
            }
        }

        function method get_aggregation_bits...
        ensures 
                var s := get_aggregation_bits(index);
                && |s| == index
                && forall i | 0 <= i < |s| :: if i == index - 1 then s[i] else !s[i]         

        // Helper functions/lemmas used when proving the postcondition of method listen_for_attestation_shares below
        predicate f_listen_for_attestation_shares_helper_2(
            process: Att_DVCState,
            attestation_share: AttestationShare
        )
        {
            var activate_att_consensus_intances := process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

                || (activate_att_consensus_intances == {} && !process.latest_attestation_duty.isPresent())
                || (activate_att_consensus_intances != {} && minInSet(activate_att_consensus_intances) <= attestation_share.data.slot)
                || (activate_att_consensus_intances == {} && process.current_attestation_duty.isPresent() && process.current_attestation_duty.safe_get().slot <= attestation_share.data.slot)                
                || (activate_att_consensus_intances == {} && !process.current_attestation_duty.isPresent() && process.latest_attestation_duty.isPresent() && process.latest_attestation_duty.safe_get().slot < attestation_share.data.slot)     
        } 

        function f_listen_for_attestation_shares_helper(
            process: Att_DVCState,
            attestation_share: AttestationShare
        ): Att_DVCState
        {
            var activate_att_consensus_intances := process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;

            var k := (attestation_share.data, attestation_share.aggregation_bits);
            var attestation_shares_db_at_slot := getOrDefault(process.rcvd_attestation_shares, attestation_share.data.slot, map[]);
            
            var new_attestation_shares_db := 
                    process.rcvd_attestation_shares[
                        attestation_share.data.slot := 
                            attestation_shares_db_at_slot[
                                        k := 
                                            getOrDefault(attestation_shares_db_at_slot, k, {}) + 
                                            {attestation_share}
                                        ]
                            ];

            process.(
                rcvd_attestation_shares := new_attestation_shares_db
            )
        }        

        method listen_for_attestation_shares...
        ensures old(isValidReprExtended()) ==> 
                        && isValidReprExtended()
                        && f_listen_for_attestation_shares(old(toAtt_DVCState()), attestation_share) == toAtt_DVCStateAndOuputs();
        {
            ...;
            if...
            {
                if  old(isValidReprExtended())
                {
                    forall e | e in old(toAtt_DVCState()).attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
                    ensures e in att_consensus.consensus_instances_started.Keys
                    {
                        lemmaMapKeysHasOneEntryInItems(old(toAtt_DVCState()).attestation_consensus_engine_state.active_attestation_consensus_instances, e);
                    }                 
                    forall e | e in att_consensus.consensus_instances_started.Keys
                    ensures e in old(toAtt_DVCState()).attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;
                    {
                        lemmaMapKeysHasOneEntryInItems(att_consensus.consensus_instances_started, e);
                    }                  
                    assert att_consensus.consensus_instances_started.Keys <= old(toAtt_DVCState()).attestation_consensus_engine_state.active_attestation_consensus_instances.Keys;
                    assert old(isValidReprExtended()) ==>  f_listen_for_attestation_shares_helper_2(old(toAtt_DVCState()), attestation_share);
                }
                ...;
                if...
                {
                assert old(isValidReprExtended()) ==> 
                        && isValidReprExtended()
                        && f_listen_for_attestation_shares_helper(old(toAtt_DVCState()), attestation_share) == toAtt_DVCState();                      
                    ...;
                }
                assert old(isValidReprExtended()) ==> 
                        && isValidReprExtended()
                        && f_listen_for_attestation_shares(old(toAtt_DVCState()), attestation_share).state == toAtt_DVCState();                          
            }
            else
            {
                assert old(isValidReprExtended()) ==> 
                            && isValidReprExtended()
                            && f_listen_for_attestation_shares(old(toAtt_DVCState()), attestation_share) == toAtt_DVCStateAndOuputs();
            }
        }

        // Helper function/lemmas used when proving the postcondition of method listen_for_new_imported_blocks below
        function f_listen_for_new_imported_blocks_part_1_for_loop_inv(
            process: Att_DVCState,
            block: BeaconBlock,
            i: Slot
        ) : (new_att: map<Slot, AttestationData>)
        requires i <= |block.body.attestations|
        requires f_listen_for_new_imported_blocks.requires(process, block)
        {            
            map a |
                    && a in block.body.attestations[..i]
                    && isMyAttestation(a, process.bn, block, bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey))
                ::
                    a.data.slot := a.data
        }  

        predicate p_listen_for_new_imported_blocks_part_2_for_loop_inv(
            process: Att_DVCState,
            block: BeaconBlock,
            i: Slot,
            a2: map<Slot, AttestationData>
        ) 
        requires i <= |block.body.attestations|
        requires f_listen_for_new_imported_blocks.requires(process, block)
        {
            a2 == process.future_att_consensus_instances_already_decided + f_listen_for_new_imported_blocks_part_1_for_loop_inv(process, block, i)
        }        

        lemma lem_f_listen_for_new_imported_blocks_part_1_to_2_for_loop_inv(
            process: Att_DVCState,
            block: BeaconBlock,
            i: Slot,
            a1: map<Slot, AttestationData>,
            a2: map<Slot, AttestationData>
        ) 
        requires i < |block.body.attestations|
        requires f_listen_for_new_imported_blocks.requires(process, block)        
        requires var valIndex := bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);
                && a1 == process.future_att_consensus_instances_already_decided + f_listen_for_new_imported_blocks_part_1_for_loop_inv(process, block, i)
                && var a := block.body.attestations[i]; a2 == if isMyAttestation(a,process.bn, block, valIndex) then 
                            a1[a.data.slot := a.data]
                        else 
                            a1
        ensures p_listen_for_new_imported_blocks_part_2_for_loop_inv(process, block, i + 1, a2)
        {
            // Yes!!! The following is needed to allow Dafny prove the lemma!!!
            var a := block.body.attestations[i];
            if isMyAttestation(a,process.bn, block, bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey)) 
            {
                
            }
        }

        predicate p_listen_for_new_imported_blocks_part_2(
            process: Att_DVCState,
            block: BeaconBlock,
            a1: map<Slot, AttestationData>
        ) 
        requires f_listen_for_new_imported_blocks_part_1.requires(process, block)
        {
            a1 == process.future_att_consensus_instances_already_decided + f_listen_for_new_imported_blocks_part_1(process, block)
        }


        lemma lem_p_listen_for_new_imported_blocks_part_2_for_loop_inv_to_part_2(
            process: Att_DVCState,
            block: BeaconBlock,
            a1: map<Slot, AttestationData>
        ) 
        requires f_listen_for_new_imported_blocks.requires(process, block)        
        requires    var valIndex := bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);
                    p_listen_for_new_imported_blocks_part_2_for_loop_inv(process, block,|block.body.attestations|, a1)
        ensures a1 == process.future_att_consensus_instances_already_decided + f_listen_for_new_imported_blocks_part_1(process, block);
        ensures p_listen_for_new_imported_blocks_part_2(process, block, a1)
        ensures f_listen_for_new_imported_blocks_part_2(process, block).attestation_consensus_engine_state.active_attestation_consensus_instances == process.attestation_consensus_engine_state.active_attestation_consensus_instances - a1.Keys
        {

        }        

        function f_listen_for_new_imported_blocks_part_1(
            process: Att_DVCState,
            block: BeaconBlock
        ): map<Slot, AttestationData>
       requires f_listen_for_new_imported_blocks.requires(process, block)       
        {
            var valIndex := bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);
                
            map a |
                    && a in block.body.attestations
                    && isMyAttestation(a, process.bn, block, valIndex)
                ::
                    a.data.slot := a.data

        }         

        function f_listen_for_new_imported_blocks_part_2(
            process: Att_DVCState,
            block: BeaconBlock
        ): Att_DVCState
        requires f_listen_for_new_imported_blocks.requires(process, block)        
        {
            var valIndex := bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);
                
            var s := map a |
                    && a in block.body.attestations
                    && isMyAttestation(a, process.bn, block, valIndex)
                ::
                    a.data.slot := a.data;

            var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + s;

            process.(
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys 
            )      

        }   

        function f_listen_for_new_imported_blocks_part_3(
            process: Att_DVCState,
            block: BeaconBlock
        ): Att_DVCState
        requires f_listen_for_new_imported_blocks.requires(process, block)        
        {
            var valIndex := bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);
                
            var s := map a |
                    && a in block.body.attestations
                    && isMyAttestation(a, process.bn, block, valIndex)
                ::
                    a.data.slot := a.data;

            var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + s;

            var new_future_att_consensus_instances_already_decided := 
                    if process.latest_attestation_duty.isPresent() then
                        var old_instances := 
                                set i | 
                                    && i in att_consensus_instances_already_decided.Keys
                                    && i <= process.latest_attestation_duty.safe_get().slot
                                ;
                        att_consensus_instances_already_decided - old_instances
                    else
                        att_consensus_instances_already_decided
                        ;

            process.(
                    future_att_consensus_instances_already_decided := new_future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys 
            )      
        }    

        function f_listen_for_new_imported_blocks_part_4(
            process: Att_DVCState,
            block: BeaconBlock
        ): Att_DVCState
        requires f_listen_for_new_imported_blocks.requires(process, block)        
        requires 
            var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + f_listen_for_new_imported_blocks_part_1(process, block);
        
        process.current_attestation_duty.isPresent() && process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided        
        {
            var valIndex := bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);
                
            var s := map a |
                    && a in block.body.attestations
                    && isMyAttestation(a, process.bn, block, valIndex)
                ::
                    a.data.slot := a.data;

            var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + s;

            var new_future_att_consensus_instances_already_decided := 
                    if process.latest_attestation_duty.isPresent() then
                        var old_instances := 
                                set i | 
                                    && i in att_consensus_instances_already_decided.Keys
                                    && i <= process.latest_attestation_duty.safe_get().slot
                                ;
                        att_consensus_instances_already_decided - old_instances
                    else
                        att_consensus_instances_already_decided
                        ;


            var attestation_consensus_engine_state_after_stop := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    );    

            var decided_attestation_data := att_consensus_instances_already_decided[process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);                            

            process.(
                    future_att_consensus_instances_already_decided := new_future_att_consensus_instances_already_decided,
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys,
                    current_attestation_duty := None,
                    attestation_slashing_db := new_attestation_slashing_db,
                    attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                        attestation_consensus_engine_state_after_stop,
                        new_attestation_slashing_db
                    )                  
            )      
        }                   
      
        function f_listen_for_new_imported_blocks_part_3_calc_old_instances(
            att_consensus_instances_already_decided: map<Slot, AttestationData>
        ): set<Slot>
        requires toAtt_DVCState().latest_attestation_duty.isPresent()
        reads toAtt_DVCState.reads
        {
            set i | 
                && i in att_consensus_instances_already_decided.Keys
                && i <= toAtt_DVCState().latest_attestation_duty.safe_get().slot
                              
        }        

        twostate lemma lem_listen_for_new_imported_blocks_from_part_2_to_3_latest_attestation_duty_present(
            p0: Att_DVCState,
            att_consensus_instances_already_decided: map<Slot, AttestationData>,
            old_instances: set<Slot>,
            block: BeaconBlock
        )      
        requires&& (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block)) 
                && old(latest_attestation_duty).isPresent()
                && latest_attestation_duty.isPresent()
                && p0 == f_listen_for_new_imported_blocks_part_2(old(toAtt_DVCState()), block) 
            
                && att_consensus_instances_already_decided == old(toAtt_DVCState()).future_att_consensus_instances_already_decided + f_listen_for_new_imported_blocks_part_1(old(toAtt_DVCState()), block)

                && old_instances == f_listen_for_new_imported_blocks_part_3_calc_old_instances(att_consensus_instances_already_decided)
                && toAtt_DVCState() == p0.(
                        future_att_consensus_instances_already_decided := att_consensus_instances_already_decided - old_instances
                    )
        ensures
                toAtt_DVCState() == f_listen_for_new_imported_blocks_part_3(old(toAtt_DVCState()), block);  
        {
            
        }    

        twostate lemma lem_listen_for_new_imported_blocks_from_part_2_to_3_latest_attestation_duty_not_present(
            p0: Att_DVCState,
            att_consensus_instances_already_decided: map<Slot, AttestationData>,
            block: BeaconBlock
        )      
        requires&& (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block)) 
                && !old(latest_attestation_duty).isPresent()
                && p0 == f_listen_for_new_imported_blocks_part_2(old(toAtt_DVCState()), block) 
            
                && att_consensus_instances_already_decided == old(toAtt_DVCState()).future_att_consensus_instances_already_decided + f_listen_for_new_imported_blocks_part_1(old(toAtt_DVCState()), block)

                && toAtt_DVCState() == p0.(
                        future_att_consensus_instances_already_decided := att_consensus_instances_already_decided 
                    )
        ensures
                toAtt_DVCState() == f_listen_for_new_imported_blocks_part_3(old(toAtt_DVCState()), block);  
        {
            
        }         

        twostate lemma lem_listen_for_new_imported_blocks_from_part_3_to_4(
            p0: Att_DVCState,
            block: BeaconBlock
        )      
        requires&& (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block)) 
                && p0 == f_listen_for_new_imported_blocks_part_3(old(toAtt_DVCState()), block) 
                && 
                    var att_consensus_instances_already_decided := old(toAtt_DVCState()).future_att_consensus_instances_already_decided + f_listen_for_new_imported_blocks_part_1(old(toAtt_DVCState()), block);
                &&         old(toAtt_DVCState()).current_attestation_duty.isPresent() && old(toAtt_DVCState()).current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided 
                &&
                    var decided_attestation_data := att_consensus_instances_already_decided[old(toAtt_DVCState()).current_attestation_duty.safe_get().slot];
                    var new_attestation_slashing_db := f_update_attestation_slashing_db(old(toAtt_DVCState()).attestation_slashing_db, decided_attestation_data); 
                && toAtt_DVCState() == p0.(
                        current_attestation_duty := None,
                        attestation_slashing_db := new_attestation_slashing_db,
                        attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                            p0.attestation_consensus_engine_state,
                            new_attestation_slashing_db
                        )                             
                    )
        ensures
                toAtt_DVCState() == f_listen_for_new_imported_blocks_part_4(old(toAtt_DVCState()), block);  
        {
            
        }      

        twostate predicate lem_listen_for_new_imported_blocks_from_part_4_to_full_current_attestation_duty_has_already_been_decided_precondition(
            p0: Att_DVCState,
            att_consensus_instances_already_decided: map<Slot, AttestationData>,
            block: BeaconBlock
        )      
        reads toAtt_DVCState.reads
        { 
            && (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block)) 
            && old(current_attestation_duty).isPresent()
            && p_listen_for_new_imported_blocks_part_2(old(toAtt_DVCState()), block, att_consensus_instances_already_decided)
            && old(current_attestation_duty).safe_get().slot in att_consensus_instances_already_decided
            && p0 == f_listen_for_new_imported_blocks_part_4(old(toAtt_DVCState()), block) 
            && f_check_for_next_duty.requires(p0)

            && toAtt_DVCState() == f_check_for_next_duty(p0).state
        }

        twostate lemma lem_listen_for_new_imported_blocks_from_part_4_to_full_current_attestation_duty_has_already_been_decided(
            p0: Att_DVCState,
            att_consensus_instances_already_decided: map<Slot, AttestationData>,
            block: BeaconBlock
        )      
        requires lem_listen_for_new_imported_blocks_from_part_4_to_full_current_attestation_duty_has_already_been_decided_precondition(p0, att_consensus_instances_already_decided, block)
        ensures
                toAtt_DVCState()  == f_listen_for_new_imported_blocks(old(toAtt_DVCState()), block).state;
        {
            var process := old(toAtt_DVCState());
            var valIndex := bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);
            
            var s := map a |
                    && a in block.body.attestations
                    && isMyAttestation(a, process.bn, block, valIndex)
                ::
                    a.data.slot := a.data;

            var att_consensus_instances_already_decided_let := process.future_att_consensus_instances_already_decided + s;

            assert att_consensus_instances_already_decided_let == old(toAtt_DVCState()).future_att_consensus_instances_already_decided + f_listen_for_new_imported_blocks_part_1(old(toAtt_DVCState()), block);

            var future_att_consensus_instances_already_decided := 
                    if process.latest_attestation_duty.isPresent() then
                        var old_instances := 
                                set i | 
                                    && i in att_consensus_instances_already_decided_let.Keys
                                    && i <= process.latest_attestation_duty.safe_get().slot
                                ;
                        att_consensus_instances_already_decided_let - old_instances
                    else
                        att_consensus_instances_already_decided_let
                            ;

            var newProcess :=
                    process.(
                        future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                        attestation_consensus_engine_state := stopConsensusInstances(
                                        process.attestation_consensus_engine_state,
                                        att_consensus_instances_already_decided_let.Keys
                        ),
                        attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided_let.Keys,
                        rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided_let.Keys                    
                    );    

            var decided_attestation_data := att_consensus_instances_already_decided[process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);
            var newProces2 := newProcess.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    newProcess.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );
            var r := f_check_for_next_duty(newProces2);
            assert newProcess.current_attestation_duty ==  process.current_attestation_duty;       

            assert p0 == newProces2;   
            assert newProcess.current_attestation_duty.isPresent() && newProcess.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided_let ;
            assert att_consensus_instances_already_decided_let == att_consensus_instances_already_decided;

            assert || f_check_for_next_duty(newProces2) == f_listen_for_new_imported_blocks(process, block) 
            by 
            {
                assert forall a, b :: a == b &&  (f_check_for_next_duty.requires(a) ||  f_check_for_next_duty.requires(b)) ==> f_check_for_next_duty(a) == f_check_for_next_duty(b);
            }
                  
        }             
        

        twostate lemma lem_listen_for_new_imported_blocks_from_part_3_to_full_current_attestation_duty_has_not_already_been_decided(
            block: BeaconBlock,
            att_consensus_instances_already_decided: map<Slot, AttestationData>
        )      
        requires&& (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block)) 
                && att_consensus_instances_already_decided == old(toAtt_DVCState()).future_att_consensus_instances_already_decided + f_listen_for_new_imported_blocks_part_1(old(toAtt_DVCState()), block)
                && 
                    (
                        || !old(current_attestation_duty).isPresent()
                        || old(current_attestation_duty).safe_get().slot !in att_consensus_instances_already_decided
                    )
                && toAtt_DVCState() == f_listen_for_new_imported_blocks_part_3(old(toAtt_DVCState()), block) 
        ensures
                toAtt_DVCState()  == f_listen_for_new_imported_blocks(old(toAtt_DVCState()), block).state;
        {
                              
        }                 

        lemma f_listen_for_new_imported_blocks_empty_outputs(
            process: Att_DVCState,
            block: BeaconBlock
        )
        requires f_listen_for_new_imported_blocks.requires(process, block)
        ensures f_listen_for_new_imported_blocks(process, block).outputs == getEmptyOuputs()
        {
            forall p | f_check_for_next_duty.requires(p)
            ensures f_check_for_next_duty(p).outputs == getEmptyOuputs()
            {
                f_check_for_next_duty_empty_outputs(p);
            }
        }

        // TODO: Type issues
        lemma f_check_for_next_duty_empty_outputs(
            process: Att_DVCState
        )
        requires f_check_for_next_duty.requires(process, attestation_duty)
        
        ensures f_check_for_next_duty(process).outputs == getEmptyOuputs()
        {
            if  && process.attestation_duties_queue != [] 
                && (
                    || process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided
                    || !process.current_attestation_duty.isPresent()
                )    
            {
                
                    if process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided.Keys 
                    {
                        var queue_head := process.attestation_duties_queue[0];
                        var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, process.future_att_consensus_instances_already_decided[queue_head.slot]);
                        f_check_for_next_duty_empty_outputs(process.(
                            attestation_duties_queue := process.attestation_duties_queue[1..],
                            attestation_slashing_db := new_attestation_slashing_db,
                            attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                                process.attestation_consensus_engine_state,
                                new_attestation_slashing_db
                            )                        
                        ));
                        assert f_check_for_next_duty(process).outputs == getEmptyOuputs();       
                    }
                    else
                    {
                        var new_process := process.(
                            attestation_duties_queue := process.attestation_duties_queue[1..]
                        );  
                        assert f_check_for_next_duty(process).outputs == getEmptyOuputs();       
                    }
            }
                    
            else 
            {
                assert f_check_for_next_duty(process).outputs == getEmptyOuputs();
            }
         
        }     

        twostate lemma lemaUnchangedThatImpliesEmptyOutputs()
        requires
            && unchanged(network`att_shares_sent)
            && unchanged(bn`attestations_submitted)
        ensures toAtt_DVCStateAndOuputs().outputs == getEmptyOuputs()
        {

        }        

        // Now that a bunch of {:fuel xxx, 0, 0} attributes have been added to listen_for_new_imported_blocks, this lemma does not seem tob be required anymore. Leaving it here, with its own old comment, just in case.
        // 
        // As the name of the lemma suggests, this is an unused lemma which, however, if commented out, very very very
        // surprisingly, causes the verification time of the method listen_for_new_imported_blocks to increase to more
        // than 30 min. lemma
        // unused_lem_that_if_commented_out_gets_the_verification_time_of_the_following_method_to_increase_to_30_plus_min(
        // process: Att_DVCState, block: BeaconBlock
        // )
        // requires f_listen_for_new_imported_blocks.requires(process, block)  
        // requires process.latest_attestation_duty.isPresent()                   
        // ensures  f_listen_for_new_imported_blocks_part_3.requires(process, block) ensures  var
        // att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided +
        // f_listen_for_new_imported_blocks_part_1(process, block); var old_instances := set i | && i in
        // att_consensus_instances_already_decided.Keys && i <= process.latest_attestation_duty.safe_get().slot
        //                 ;                
        // f_listen_for_new_imported_blocks_part_3(process, block).future_att_consensus_instances_already_decided ==
        // att_consensus_instances_already_decided - old_instances
        // {
            
        // }            

        // 6min - 3.7.1
        method  
        {:fuel f_check_for_next_duty, 0, 0} 
        {:fuel f_update_attestation_slashing_db, 0, 0} 
        {:fuel f_listen_for_new_imported_blocks_part_3, 0, 0}
        {:fuel f_listen_for_new_imported_blocks_part_4, 0, 0}
        {:fuel f_listen_for_new_imported_blocks, 0, 0}
        listen_for_new_imported_blocks...
        ensures (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block)) ==> 
                    && isValidReprExtended()
                    && s.Success?
                    && f_listen_for_new_imported_blocks(old(toAtt_DVCState()), block) == toAtt_DVCStateAndOuputs()
        {
            assert (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block)) ==> block.body.state_root in bn.state_roots_of_imported_blocks;
            ...;
            while...
                invariant 0 <= i <= |block.body.attestations|
                invariant ValidRepr() && fresh(bn.Repr - old(bn.Repr)) 
            && unchanged(rs)
            && unchanged(network)
            && unchanged(att_consensus)
            && unchanged(att_consensus.consensus_instances_started.Values)
            && unchanged(this)
            && unchanged(att_consensus.Repr)
            && unchanged(bn`state_roots_of_imported_blocks)
            && unchanged(bn`attestations_submitted)
                invariant  old(isValidReprExtended()) ==> isValidReprExtended();       
                invariant old(isValidReprExtended()) ==> lemmaConsensusInstancesAreTheSamePrecond(att_consensus)       
                invariant old(isValidReprExtended() )==> toAtt_DVCState() == old(toAtt_DVCState()) 
                invariant unchanged(bn`attestations_submitted)
                invariant this as object != att_consensus
                invariant this !in att_consensus.Repr

                invariant (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block)) ==> p_listen_for_new_imported_blocks_part_2_for_loop_inv(old(toAtt_DVCState()), block, i, att_consensus_instances_already_decided)                
            {
                var ax := att_consensus_instances_already_decided;
                ...;
                if...
                {
                    ...;
                    
               

                }
                if (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block)){
                    lem_f_listen_for_new_imported_blocks_part_1_to_2_for_loop_inv(old(toAtt_DVCState()), block, i, ax, att_consensus_instances_already_decided);
                }

                ...;    
            }
            assert (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block)) ==>
                && p_listen_for_new_imported_blocks_part_2(old(toAtt_DVCState()), block, att_consensus_instances_already_decided)
                by
            {
                if (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block)){
                        assert isValidReprExtended();   
                        assert lemmaConsensusInstancesAreTheSamePrecond(att_consensus);                
                        lem_p_listen_for_new_imported_blocks_part_2_for_loop_inv_to_part_2(old(toAtt_DVCState()), block, att_consensus_instances_already_decided);
                }   
            }       
 
            ...;

            if...
            {

                
                var o1 := toAtt_DVCState();
                label L2:
                assert (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block)) ==> 
                    && o1 == f_listen_for_new_imported_blocks_part_2(old(toAtt_DVCState()), block) 
                    && isValidReprExtended()
                    && f_check_for_next_duty.requires(toAtt_DVCState())
                    && unchanged(`current_attestation_duty)
                    && p_listen_for_new_imported_blocks_part_2(old(toAtt_DVCState()), block, att_consensus_instances_already_decided)
                by
                {
                    if  (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block))
                    {
                        assert isValidReprExtended();
                        assert lemmaConsensusInstancesHaveBeenRemovedPrecond(att_consensus, att_consensus_instances_already_decided.Keys);
                        lemmaConsensusInstancesHaveBeenRemoved(att_consensus, att_consensus_instances_already_decided.Keys);

                        assert f_listen_for_new_imported_blocks_part_2(old(toAtt_DVCState()), block).attestation_consensus_engine_state.active_attestation_consensus_instances == old(toAtt_DVCState()).attestation_consensus_engine_state.active_attestation_consensus_instances - att_consensus_instances_already_decided.Keys;

                        calc {
                            o1;
                            { lemmaConsensusInstancesAreTheSame@L2(att_consensus);}
                            toAtt_DVCState();
                            f_listen_for_new_imported_blocks_part_2(old(toAtt_DVCState()), block);        
                        }

                        assert o1 == f_listen_for_new_imported_blocks_part_2(old(toAtt_DVCState()), block);   

                        assert unchanged(`current_attestation_duty);                                                
                    }
                }
                
                
                ...;
                var o2 := toAtt_DVCState();        
                assert (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block)) ==>  
                    && o2 == f_listen_for_new_imported_blocks_part_3(old(toAtt_DVCState()), block)
                    && isValidReprExtended()  
                    && f_check_for_next_duty.requires(toAtt_DVCState())
                    && unchanged(`current_attestation_duty)
                    && p_listen_for_new_imported_blocks_part_2(old(toAtt_DVCState()), block, att_consensus_instances_already_decided)
                by
                {
                    if  (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block))
                    {
                        lemmaConsensusInstancesAreTheSame@L2(att_consensus);
                        assert o2 == o1.(
                            future_att_consensus_instances_already_decided := att_consensus_instances_already_decided - old_instances
                        );
                        lem_listen_for_new_imported_blocks_from_part_2_to_3_latest_attestation_duty_present(o1, att_consensus_instances_already_decided, old_instances, block);
                        assert unchanged(`current_attestation_duty);                                                   
                    }  
                } 
            }
            else
            {
                var o1 := toAtt_DVCState();
                label L2:
                assert (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block)) ==> 
                        && o1 == f_listen_for_new_imported_blocks_part_2(old(toAtt_DVCState()), block) 
                        && isValidReprExtended()
                        && f_check_for_next_duty.requires(toAtt_DVCState())
                        && unchanged(`current_attestation_duty)
                        && p_listen_for_new_imported_blocks_part_2(old(toAtt_DVCState()), block, att_consensus_instances_already_decided)
                by
                {
                    if  (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block))
                    {
                        assert isValidReprExtended();
                        assert lemmaConsensusInstancesHaveBeenRemovedPrecond(att_consensus, att_consensus_instances_already_decided.Keys);
                        lemmaConsensusInstancesHaveBeenRemoved(att_consensus, att_consensus_instances_already_decided.Keys);

                        assert f_listen_for_new_imported_blocks_part_2(old(toAtt_DVCState()), block).attestation_consensus_engine_state.active_attestation_consensus_instances == old(toAtt_DVCState()).attestation_consensus_engine_state.active_attestation_consensus_instances - att_consensus_instances_already_decided.Keys;

                        calc {
                            o1;
                            { lemmaConsensusInstancesAreTheSame@L2(att_consensus);}
                            toAtt_DVCState();
                            f_listen_for_new_imported_blocks_part_2(old(toAtt_DVCState()), block);        
                        }

                        assert o1 == f_listen_for_new_imported_blocks_part_2(old(toAtt_DVCState()), block);            
                        assert unchanged(`current_attestation_duty);                                        
                    }
                }
                ...;

                var o2 := toAtt_DVCState();        
                assert (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block)) ==>  
                    && o2 == f_listen_for_new_imported_blocks_part_3(old(toAtt_DVCState()), block)  
                    && isValidReprExtended()
                    && f_check_for_next_duty.requires(toAtt_DVCState())
                    && unchanged(`current_attestation_duty)
                    && p_listen_for_new_imported_blocks_part_2(old(toAtt_DVCState()), block, att_consensus_instances_already_decided)
                by
                {
                    if  (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block))
                    {
                        assert isValidReprExtended();   

                        var o2 := toAtt_DVCState();
                        lemmaConsensusInstancesAreTheSame@L2(att_consensus);
                        assert o2 == o1.(
                            future_att_consensus_instances_already_decided := att_consensus_instances_already_decided 
                        );
                        lem_listen_for_new_imported_blocks_from_part_2_to_3_latest_attestation_duty_not_present(o1, att_consensus_instances_already_decided, block);
                        assert unchanged(`current_attestation_duty);                                                                    
                    } 
                }                                         
            }     

            if...
            {
                label L3:
                var o3 := toAtt_DVCState();
                assert (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block)) ==>  
                    && toAtt_DVCState() == f_listen_for_new_imported_blocks_part_3(old(toAtt_DVCState()), block)
                    && isValidReprExtended()
                    && f_check_for_next_duty.requires(toAtt_DVCState())
                    && unchanged(`current_attestation_duty)
                    && p_listen_for_new_imported_blocks_part_2(old(toAtt_DVCState()), block, att_consensus_instances_already_decided)
                    && old(current_attestation_duty).safe_get().slot in att_consensus_instances_already_decided
                    ;
                
                ...;
                {
                    var o4 := toAtt_DVCState();
                    assert (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block)) ==>  
                        && o4 == f_listen_for_new_imported_blocks_part_4(old(toAtt_DVCState()), block)
                        && isValidReprExtended()
                        && f_check_for_next_duty.requires(toAtt_DVCState())
                        && old(current_attestation_duty).safe_get().slot in att_consensus_instances_already_decided
                        && p_listen_for_new_imported_blocks_part_2(old(toAtt_DVCState()), block, att_consensus_instances_already_decided)
                    by 
                    {
                        if  (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block))
                        {
                            lemmaAttestationHasBeenAddedToSlashingDbForall@L3(att_consensus_instances_already_decided[old@L3(current_attestation_duty).safe_get().slot]);
                            lem_listen_for_new_imported_blocks_from_part_3_to_4(o3, block);
                            assert o4 == f_listen_for_new_imported_blocks_part_4(old(toAtt_DVCState()), block);  
                        }
                    } 
                    
                    ...;
                    assert (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block)) ==>  toAtt_DVCState() == f_listen_for_new_imported_blocks(old(toAtt_DVCState()), block).state by       
                    {
                        if  (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block))
                        {
                            assert lem_listen_for_new_imported_blocks_from_part_4_to_full_current_attestation_duty_has_already_been_decided_precondition(o4, att_consensus_instances_already_decided, block) by 
                            {
                                assert 
                                && p_listen_for_new_imported_blocks_part_2(old(toAtt_DVCState()), block, att_consensus_instances_already_decided)
                                && old(current_attestation_duty).safe_get().slot in att_consensus_instances_already_decided
                                && o4 == f_listen_for_new_imported_blocks_part_4(old(toAtt_DVCState()), block) 
                                && f_check_for_next_duty.requires(o4)
                                && toAtt_DVCState() == f_check_for_next_duty(o4).state
                                ;                                
                            }    

                            lem_listen_for_new_imported_blocks_from_part_4_to_full_current_attestation_duty_has_already_been_decided(o4, att_consensus_instances_already_decided, block);  
                        }
                    }                                   

                }
            }
            else
            {
                var o3 := toAtt_DVCState();
                assert (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block)) ==>  
                    && toAtt_DVCState() == f_listen_for_new_imported_blocks_part_3(old(toAtt_DVCState()), block)
                    && isValidReprExtended()
                    && f_check_for_next_duty.requires(toAtt_DVCState())
                    && unchanged(`current_attestation_duty)
                    ;
                if  (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block))
                {
                    // assert !old(current_attestation_duty).isPresent();
                    lem_listen_for_new_imported_blocks_from_part_3_to_full_current_attestation_duty_has_not_already_been_decided(block, att_consensus_instances_already_decided);
                }
            }
            if  (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toAtt_DVCState()), block))
            {
                assert toAtt_DVCState() == f_listen_for_new_imported_blocks(old(toAtt_DVCState()), block).state;  
                assert unchanged(network);
                assert unchanged(bn`attestations_submitted);
                lemaUnchangedThatImpliesEmptyOutputs();
                f_listen_for_new_imported_blocks_empty_outputs(old(toAtt_DVCState()), block);               
            }            
            ...;
        }

        method resend_attestation_share...
        ensures old(isValidReprExtended()) ==>
                                && isValidReprExtended()
                                && f_resend_attestation_share(old(toAtt_DVCState())) == toAtt_DVCStateAndOuputs()
        {
            ...;
            assert  old(isValidReprExtended()) ==> f_resend_attestation_share(old(toAtt_DVCState())).state == toAtt_DVCStateAndOuputs().state;
            var setWithRecipient := set att_share | att_share in attestation_shares_to_broadcast.Values :: addRecepientsToMessage(att_share, peers);
            var setWithRecipientFlattened := setUnion(setWithRecipient);
            assert old(isValidReprExtended()) ==>network.att_shares_sent == old(network.att_shares_sent) +[setWithRecipientFlattened];                
            assert old(isValidReprExtended()) ==>seqMinusToSet(network.att_shares_sent, old(network.att_shares_sent)) == {setWithRecipientFlattened};
            assert  old(isValidReprExtended()) ==>toAtt_DVCStateAndOuputs().outputs.att_shares_sent == setWithRecipientFlattened;
            assert  old(isValidReprExtended()) ==>f_resend_attestation_share(old(toAtt_DVCState())) == toAtt_DVCStateAndOuputs();                  
        }
    }
}

// Keep this here as it does come handy from time to time
// var o := toAtt_DVCState();
// var rs := r.state;

// assert rs.attestation_consensus_engine_state == o.attestation_consensus_engine_state;

// assert rs == o.(
//     // current_attestation_duty := rs.current_attestation_duty,
//     latest_attestation_duty := rs.latest_attestation_duty,
//     attestation_duties_queue := rs.attestation_duties_queue,
//     attestation_slashing_db := rs.attestation_slashing_db,
//     rcvd_attestation_shares := rs.rcvd_attestation_shares,
//     attestation_shares_to_broadcast := rs.attestation_shares_to_broadcast,
//     // attestation_consensus_engine_state := rs.attestation_consensus_engine_state,
//     // attestation_validity_check
//     peers := rs.peers,
//     construct_signed_attestation_signature := rs.construct_signed_attestation_signature,
//     // TODO := rs.// TODO,
//     dv_pubkey := rs.dv_pubkey,
//     future_att_consensus_instances_already_decided := rs.future_att_consensus_instances_already_decided//,
//     // bn := rs.bn//,
//     // rs := rs.rs
// )
// ;  