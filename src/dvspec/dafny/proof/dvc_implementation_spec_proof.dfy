include "../commons.dfy"
include "../specification/dvc_spec.dfy"

module DVCNode_Implementation_Proofs refines DVCNode_Implementation
{
    import opened DVCNode_Spec
    import opened DVCNode_Externs = DVCNode_Externs_Proofs

    function toAttestationConsensusValidityCheckState(
        acvc: ConsensusValidityCheck<AttestationData>
    ): AttestationConsensusValidityCheckState
    requires isAttestationConsensusValidityCheck(acvc)
    reads acvc, (acvc as AttestationConsensusValidityCheck).dvcNode`attestation_slashing_db
    {
        var attestation_duty := (acvc as AttestationConsensusValidityCheck).attestation_duty;
        var attestation_slashing_db := (acvc as AttestationConsensusValidityCheck).dvcNode.attestation_slashing_db;
        AttestationConsensusValidityCheckState(
            attestation_duty := attestation_duty,
            attestation_slashing_db := attestation_slashing_db,
            validityPredicate := (ad: AttestationData) => consensus_is_valid_attestation_data(attestation_slashing_db, ad, attestation_duty)
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
    
    function get_attestation_consensus_active_instances(
        m: map<Slot, ConsensusValidityCheck<AttestationData>>
    ): (r: map<Slot, AttestationConsensusValidityCheckState>)
    reads m.Values, set v: ConsensusValidityCheck<AttestationData>  | && v in m.Values && isAttestationConsensusValidityCheck(v) :: toAttestationConsensusValidityCheck(v).dvcNode`attestation_slashing_db
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
    reads ce, ce.consensus_instances_started.Values, set v: ConsensusValidityCheck<AttestationData>  | && v in ce.consensus_instances_started.Values && isAttestationConsensusValidityCheck(v) :: toAttestationConsensusValidityCheck(v).dvcNode`attestation_slashing_db
    {
        ConsensusEngineState(
            attestation_consensus_active_instances := get_attestation_consensus_active_instances(ce.consensus_instances_started)   
        )
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


    class DVCNode...
    {
        function toDVCNodeState(): DVCNodeState
        reads this, bn, rs, att_consensus, att_consensus.consensus_instances_started.Values, set v: ConsensusValidityCheck<AttestationData>  | && v in att_consensus.consensus_instances_started.Values && isAttestationConsensusValidityCheck(v) :: toAttestationConsensusValidityCheck(v).dvcNode`attestation_slashing_db
        {
            DVCNodeState(
                current_attesation_duty := current_attesation_duty,
                latest_attestation_duty := latest_attestation_duty,
                attestation_duties_queue := attestation_duties_queue,
                attestation_slashing_db := attestation_slashing_db,
                attestation_shares_db := attestation_shares_db,
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

        twostate function toDVCNodeStateAndOuputs(): DVCNodeStateAndOuputs
        reads this, network, att_consensus, bn, rs, att_consensus.consensus_instances_started.Values, set v: ConsensusValidityCheck<AttestationData>  | && v in att_consensus.consensus_instances_started.Values && isAttestationConsensusValidityCheck(v) :: toAttestationConsensusValidityCheck(v).dvcNode`attestation_slashing_db
        {
            DVCNodeStateAndOuputs(
                state := toDVCNodeState(),
                outputs := getOutputs()
            )
        }        

        predicate isValidReprExtended()
        reads *
        {
            && (forall vp | vp in att_consensus.consensus_instances_started.Values :: 
                        && isAttestationConsensusValidityCheck(vp)
                        && toAttestationConsensusValidityCheck(vp).dvcNode == this
            )
            && ValidRepr()
        }

        constructor...
        ensures 
                && isValidReprExtended()
                && Init(toDVCNodeState(), dv_pubkey, peers, construct_signed_attestation_signature, rs.pubkey)
        {
            ...;
        }

        method process_event...
        ensures (old(isValidReprExtended()) && f_process_event.requires(old(toDVCNodeState()), event)) ==>    
                && isValidReprExtended()
                && f_process_event(old(toDVCNodeState()), event) == toDVCNodeStateAndOuputs()
                && s.Success?        
        {
            ...; 

            {
                if event.ServeAttstationDuty?
                {    
                    assert (old(isValidReprExtended()) && f_process_event.requires(old(toDVCNodeState()), event)) ==> 
                        && f_process_event(old(toDVCNodeState()), event) == toDVCNodeStateAndOuputs()
                        && isValidReprExtended();
                }
                else if event.AttConsensusDecided?
                {
                    assert (old(isValidReprExtended()) && f_process_event.requires(old(toDVCNodeState()), event)) ==> 
                        && f_process_event(old(toDVCNodeState()), event) == toDVCNodeStateAndOuputs()
                        && isValidReprExtended();       
                }         
                else if event.ReceviedAttesttionShare?
                {    
                    assert (old(isValidReprExtended()) && f_process_event.requires(old(toDVCNodeState()), event)) ==> 
                        && f_process_event(old(toDVCNodeState()), event) == toDVCNodeStateAndOuputs()
                        && isValidReprExtended();  
                }              
                else if event.ImportedNewBlock? 
                {    assert (old(isValidReprExtended()) && f_process_event.requires(old(toDVCNodeState()), event)) ==> 
                        && f_process_event(old(toDVCNodeState()), event) == toDVCNodeStateAndOuputs()
                        && isValidReprExtended();  
                }              
                else if event.ResendAttestationShares?
                {    
                    assert (old(isValidReprExtended()) && f_process_event.requires(old(toDVCNodeState()), event)) ==> 
                        && f_process_event(old(toDVCNodeState()), event) == toDVCNodeStateAndOuputs()
                        && isValidReprExtended(); 
                }               
                else
                {    
                    assert (old(isValidReprExtended()) && f_process_event.requires(old(toDVCNodeState()), event)) ==> 
                        && f_process_event(old(toDVCNodeState()), event) == toDVCNodeStateAndOuputs()
                        && isValidReprExtended(); 
                }                   
                ...;
            }   
        }

        method serve_attestation_duty...
        ensures (old(isValidReprExtended()) && f_serve_attestation_duty.requires(old(toDVCNodeState()), attestation_duty)) ==> 
                && f_serve_attestation_duty(old(toDVCNodeState()), attestation_duty) == toDVCNodeStateAndOuputs()
                && isValidReprExtended()
                && s.Success?
                && unchanged(network)
                && unchanged(bn)
                && unchanged(rs)                
        {
            ...;
            {
                var o := toDVCNodeState();
                ...;
                assert o == old(toDVCNodeState()).(
                            attestation_duties_queue := old(toDVCNodeState()).attestation_duties_queue + [attestation_duty]
                        );
                assert (old(isValidReprExtended()) && f_serve_attestation_duty.requires(old(toDVCNodeState()), attestation_duty)) ==> f_serve_attestation_duty(old(toDVCNodeState()), attestation_duty) == toDVCNodeStateAndOuputs();
            }

        }

        method check_for_next_queued_duty...
        ensures (old(isValidReprExtended()) && f_check_for_next_queued_duty.requires(old(toDVCNodeState())))==> 
                && f_check_for_next_queued_duty(old(toDVCNodeState())) == toDVCNodeStateAndOuputs()
                && isValidReprExtended()
                && s.Success?
                && unchanged(network)
                && unchanged(bn)
                && unchanged(rs)                
        {
            if...
            {
                if...
                {

                    ...;
                    {
                        assert old(isValidReprExtended()) ==> isValidReprExtended();
                        ...;

                        assert (old(isValidReprExtended()) && f_check_for_next_queued_duty.requires(old(toDVCNodeState()))) ==> f_check_for_next_queued_duty(old(toDVCNodeState())) == toDVCNodeStateAndOuputs();       
                    }

                }
                else if...
                {
                    ...;
                    assert (old(isValidReprExtended()) && f_check_for_next_queued_duty.requires(old(toDVCNodeState()))) ==> f_check_for_next_queued_duty(old(toDVCNodeState())) == toDVCNodeStateAndOuputs();
                }
                else
                {
                    assert (old(isValidReprExtended()) && f_check_for_next_queued_duty.requires(old(toDVCNodeState()))) ==> f_check_for_next_queued_duty(old(toDVCNodeState())) == toDVCNodeStateAndOuputs();
                }
            }
            else
            {
                assert (old(isValidReprExtended()) && f_check_for_next_queued_duty.requires(old(toDVCNodeState()))) ==> f_check_for_next_queued_duty(old(toDVCNodeState())) == toDVCNodeStateAndOuputs();
            }
        }     

        method start_next_duty...
        ensures 
                old(isValidReprExtended()) ==>
                (
                    && isValidReprExtended()
                    && (f_start_next_duty.requires(old(toDVCNodeState()), attestation_duty) ==> 
                        && (f_start_next_duty(old(toDVCNodeState()), attestation_duty) == toDVCNodeStateAndOuputs())
                        && s.Success?
                        && unchanged(network)
                        && unchanged(bn)
                        && unchanged(rs)
                    )
                )
        {
            if old(isValidReprExtended())
            {
                forall e | e in old(att_consensus.consensus_instances_started.Keys)
                ensures e in old(get_attestation_consensus_active_instances(att_consensus.consensus_instances_started)).Keys; 
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
                                                                                     
                assert f_start_next_duty(old(toDVCNodeState()), attestation_duty) == toDVCNodeStateAndOuputs();
            }
        }

        method update_attestation_slashing_db...
        ensures f_update_attestation_slashing_db(old(toDVCNodeState()).attestation_slashing_db, attestation_data, attestation_duty_pubkey) == this.attestation_slashing_db;
        ensures  var slashing_db_attestation := SlashingDBAttestation(
                                                source_epoch := attestation_data.source.epoch,
                                                target_epoch := attestation_data.target.epoch,
                                                signing_root := Some(hash_tree_root(attestation_data)));
            attestation_slashing_db == old(attestation_slashing_db) + {slashing_db_attestation};
        {
            ...;
        }

        function f_att_consensus_decided_helper(
            process: DVCNodeState,
            id: Slot,
            decided_attestation_data: AttestationData
        ): DVCNodeStateAndOuputs
        requires process.current_attesation_duty.isPresent()
        requires forall ad | ad in process.attestation_duties_queue :: ad.slot !in process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys    
        {
            var local_current_attestation_duty := process.current_attesation_duty.safe_get();
            var attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data, local_current_attestation_duty.pubkey);

            var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
            var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
            var attestation_signature_share := rs_sign_attestation(decided_attestation_data, fork_version, attestation_signing_root, process.rs);
            // TODO: What is attestation_signature_share.aggregation_bits?
            var attestation_with_signature_share := AttestationShare(
                    aggregation_bits := get_aggregation_bits(local_current_attestation_duty.validator_index),
                    data := decided_attestation_data, 
                    signature := attestation_signature_share
                ); 

            var newProcess := 
                process.(
                    current_attesation_duty := None,
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                    attestation_slashing_db := attestation_slashing_db,
                    attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                        process.attestation_consensus_engine_state,
                        attestation_slashing_db
                    )
                )
                ;

            DVCNodeStateAndOuputs(
                newProcess,
                outputs := getEmptyOuputs().(
                    att_shares_sent := multicast(attestation_with_signature_share, process.peers)
                )                  
            )                
        }        

        method att_consensus_decided...
        ensures (old(isValidReprExtended()) && f_att_consensus_decided.requires(old(toDVCNodeState()), id, decided_attestation_data)) ==> 
                && f_att_consensus_decided(old(toDVCNodeState()), id, decided_attestation_data) == toDVCNodeStateAndOuputs()
                && isValidReprExtended()
                && r.Success?
        {
            ...;
            {
            if old(isValidReprExtended()) && f_att_consensus_decided.requires(old(toDVCNodeState()), id, decided_attestation_data)
            {
                var r := f_att_consensus_decided_helper(old(toDVCNodeState()), id, decided_attestation_data);
                var s := old(current_attesation_duty).safe_get().slot;

                forall e | e in old(toDVCNodeState()).attestation_consensus_engine_state.attestation_consensus_active_instances.Keys
                ensures e in r.state.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys
                {
                    lemmaMapKeysHasOneEntryInItems(old(toDVCNodeState()).attestation_consensus_engine_state.attestation_consensus_active_instances, e);
                }   

                assert f_att_consensus_decided_helper(old(toDVCNodeState()), id, decided_attestation_data).state == toDVCNodeStateAndOuputs().state;
            }                
                ...;
            }
            ...;
        }

        method listen_for_attestation_shares...
        ensures old(isValidReprExtended()) ==> 
                        && isValidReprExtended()
                        && f_listen_for_attestation_shares(old(toDVCNodeState()), attestation_share) == toDVCNodeStateAndOuputs();
        {
            ...;
        }

        // Helper function used when proving the postcondition of method listen_for_new_imported_blocks below
        function listen_for_new_imported_blocks_helper(
            process: DVCNodeState,
            block: BeaconBlock,
            valIndex: Optional<ValidatorIndex>,
            i: nat
        ) : (new_att: set<Slot>)
        requires i <= |block.body.attestations|
        requires block.body.state_root in process.bn.state_roots_of_imported_blocks
        {            
            set a |
                    && a in block.body.attestations[..i]
                    && isMyAttestation(a, process, block, valIndex)
                ::
                    a.data.slot
        }  


        function listen_for_new_imported_blocks_helper_2(
            process: DVCNodeState,
            block: BeaconBlock
        ): DVCNodeState
        requires block.body.state_root in process.bn.state_roots_of_imported_blocks
        {
        var valIndex := bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);
         
        var s := set a |
                && a in block.body.attestations
                && isMyAttestation(a, process, block, valIndex)
            ::
                a.data.slot;

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + s;

        var future_att_consensus_instances_already_decided := 
                if process.latest_attestation_duty.isPresent() then
                        set i | 
                            && i in att_consensus_instances_already_decided 
                            && i > process.latest_attestation_duty.safe_get().slot
                else
                    att_consensus_instances_already_decided
                        ;

            process.(
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided
            )      

        }   

        method listen_for_new_imported_blocks...
        ensures (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toDVCNodeState()), block)) ==> 
                    && isValidReprExtended()
                    && s.Success?
                    && f_listen_for_new_imported_blocks(old(toDVCNodeState()), block) == toDVCNodeStateAndOuputs()
        {
            // assert old(isValidReprExtended()) ==> isValidReprExtended();
            assert (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toDVCNodeState()), block)) ==> block.body.state_root in bn.state_roots_of_imported_blocks;
            ...;
            while...
                invariant 0 <= i <= |block.body.attestations|
                invariant ValidRepr();
                invariant  old(isValidReprExtended()) ==> isValidReprExtended();                 
                invariant block.body.state_root in bn.state_roots_of_imported_blocks;
                invariant (isValidReprExtended() && block.body.state_root in old(bn.state_roots_of_imported_blocks)) ==>
                    att_consensus_instances_already_decided == 
                    old(future_att_consensus_instances_already_decided) + listen_for_new_imported_blocks_helper(old(toDVCNodeState()), block, valIndex, i); 
                    
                invariant isValidReprExtended() ==> toDVCNodeState() == old(toDVCNodeState())
                invariant toDVCNodeStateAndOuputs().outputs == getEmptyOuputs();   
                invariant unchanged(bn`attestations_submitted)
            {

            }
            ...;
        

            if...
            {
                var o2 := toDVCNodeState();
                assert (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toDVCNodeState()), block)) ==>
            toDVCNodeState() == listen_for_new_imported_blocks_helper_2(old(toDVCNodeState()), block);    
                ...;
                assert old(isValidReprExtended()) ==> isValidReprExtended();
                assert (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toDVCNodeState()), block)) ==>
            toDVCNodeStateAndOuputs() == f_listen_for_new_imported_blocks(old(toDVCNodeState()), block);  
            }
            else
            {
                var o2 := toDVCNodeState();
                assert (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toDVCNodeState()), block)) ==>
            toDVCNodeState() == listen_for_new_imported_blocks_helper_2(old(toDVCNodeState()), block);    
                ...;
                assert old(isValidReprExtended()) ==> isValidReprExtended();                            
                assert (old(isValidReprExtended()) && f_listen_for_new_imported_blocks.requires(old(toDVCNodeState()), block)) ==>
            toDVCNodeStateAndOuputs() == f_listen_for_new_imported_blocks(old(toDVCNodeState()), block);         
            }       
            ...;
        }

        method resend_attestation_share...
        ensures old(isValidReprExtended()) ==>
                                && isValidReprExtended()
                                && f_resend_attestation_share(old(toDVCNodeState())) == toDVCNodeStateAndOuputs()
        {
            ...;
            assert  old(isValidReprExtended()) ==> f_resend_attestation_share(old(toDVCNodeState())).state == toDVCNodeStateAndOuputs().state;
            var setWithRecipient := set att_share | att_share in attestation_shares_to_broadcast.Values :: addRecepientsToMessage(att_share, peers);
            var setWithRecipientFlattened := setUnion(setWithRecipient);
            assert old(isValidReprExtended()) ==>network.att_shares_sent == old(network.att_shares_sent) +[setWithRecipientFlattened];                
            assert old(isValidReprExtended()) ==>seqMinusToSet(network.att_shares_sent, old(network.att_shares_sent)) == {setWithRecipientFlattened};
            assert  old(isValidReprExtended()) ==>toDVCNodeStateAndOuputs().outputs.att_shares_sent == setWithRecipientFlattened;
            assert  old(isValidReprExtended()) ==>f_resend_attestation_share(old(toDVCNodeState())) == toDVCNodeStateAndOuputs();                  
        }
    }
}

// Keep this here as it does come handy from time to time
// var o := toDVCNodeState();
// var rs := r.state;

// assert rs.attestation_consensus_engine_state == o.attestation_consensus_engine_state;

// assert rs == o.(
//     // current_attesation_duty := rs.current_attesation_duty,
//     latest_attestation_duty := rs.latest_attestation_duty,
//     attestation_duties_queue := rs.attestation_duties_queue,
//     attestation_slashing_db := rs.attestation_slashing_db,
//     attestation_shares_db := rs.attestation_shares_db,
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