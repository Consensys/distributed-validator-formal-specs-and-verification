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

    function toDVCNodeState(n: DVCNode): DVCNodeState
    reads n, n.bn, n.rs, n.att_consensus, n.att_consensus.consensus_instances_started.Values, set v: ConsensusValidityCheck<AttestationData>  | && v in n.att_consensus.consensus_instances_started.Values && isAttestationConsensusValidityCheck(v) :: toAttestationConsensusValidityCheck(v).dvcNode`attestation_slashing_db
    {
        DVCNodeState(
            current_attesation_duty := n.current_attesation_duty,
            latest_attestation_duty := n.latest_attestation_duty,
            attestation_duties_queue := n.attestation_duties_queue,
            attestation_slashing_db := n.attestation_slashing_db,
            attestation_shares_db := n.attestation_shares_db,
            attestation_shares_to_broadcast := n.attestation_shares_to_broadcast,
            attestation_consensus_engine_state := toConsensusEngineState(n.att_consensus),
            peers := n.peers,
            construct_signed_attestation_signature := n.construct_signed_attestation_signature,
            dv_pubkey := n.dv_pubkey,
            future_att_consensus_instances_already_decided := n.future_att_consensus_instances_already_decided,
            bn := toBNState(n.bn),
            rs := toRSState(n.rs)
        )
    }

    function seqMinusToSet<T>(s1: seq<T>, s2: seq<T>): set<T>
    {
        if |s2| <= |s1| then
            var seqDiff := s1[|s2|..];
            assert s2 <= s1 ==> s2 + seqDiff == s1;
            seqToSet(seqDiff)
        else
            {}
    }

    twostate function getOutputs(n: DVCNode): (o: Outputs)
    reads n, n.network, n.att_consensus, n.bn
    {
        Outputs(
            att_shares_sent :=  setUnion(seqMinusToSet(n.network.att_shares_sent, old(n.network.att_shares_sent))),
            attestations_submitted := seqMinusToSet(n.bn.attestations_submitted, old(n.bn.attestations_submitted))
        )
    }

    twostate function toDVCNodeStateAndOuputs(n: DVCNode): DVCNodeStateAndOuputs
    reads n, n.network, n.att_consensus, n.bn, n.rs, n.att_consensus.consensus_instances_started.Values, set v: ConsensusValidityCheck<AttestationData>  | && v in n.att_consensus.consensus_instances_started.Values && isAttestationConsensusValidityCheck(v) :: toAttestationConsensusValidityCheck(v).dvcNode`attestation_slashing_db
    {
        DVCNodeStateAndOuputs(
            state := toDVCNodeState(n),
            outputs := getOutputs(n)
        )
    }

    class DVCNode...
    {

        predicate isValid()
        reads this, this.bn, this.network, this.att_consensus, att_consensus.consensus_instances_started.Values
        {
            && (forall vp | vp in att_consensus.consensus_instances_started.Values :: 
                        && isAttestationConsensusValidityCheck(vp)
                        && toAttestationConsensusValidityCheck(vp).dvcNode == this
            )
            && {this} !! {this.bn} !! {this.network} !! {this.att_consensus} !!att_consensus.consensus_instances_started.Values
        }

        // TODO: Move to refined class?
        method process_event(
            event: Event
        ) returns (s: Status)
        modifies this, this.att_consensus, this.bn, this.network
        ensures (old(isValid()) && f_process_event.requires(old(toDVCNodeState(this)), event)) ==>    
                && isValid()
                && f_process_event(old(toDVCNodeState(this)), event) == toDVCNodeStateAndOuputs(this)
                && s.Success?        
        {
            match event {
                case ServeAttstationDuty(attestation_duty) => 
                    :- serve_attestation_duty(attestation_duty);
                case AttConsensusDecided(id, decided_attestation_data) => 
                    :- att_consensus_decided(id,  decided_attestation_data);
                case ReceviedAttesttionShare(attestation_share) => 
                    listen_for_attestation_shares(attestation_share);
                case ImportedNewBlock(block) => 
                    :- listen_for_new_imported_blocks(block);
                case ResendAttestationShares => 
                    resend_attestation_share();
                case NoEvent =>
                    
            }

            match event {
                case ServeAttstationDuty(attestation_duty) => 
                    assert (old(isValid()) && f_process_event.requires(old(toDVCNodeState(this)), event)) ==> 
                        && f_process_event(old(toDVCNodeState(this)), event) == toDVCNodeStateAndOuputs(this)
                        && isValid();
                case AttConsensusDecided(id, decided_attestation_data) => 
                    assert (old(isValid()) && f_process_event.requires(old(toDVCNodeState(this)), event)) ==> 
                        && f_process_event(old(toDVCNodeState(this)), event) == toDVCNodeStateAndOuputs(this)
                        && isValid();                
                case ReceviedAttesttionShare(attestation_share) => 
                    assert (old(isValid()) && f_process_event.requires(old(toDVCNodeState(this)), event)) ==> 
                        && f_process_event(old(toDVCNodeState(this)), event) == toDVCNodeStateAndOuputs(this)
                        && isValid();                
                case ImportedNewBlock(block) => 
                    assert (old(isValid()) && f_process_event.requires(old(toDVCNodeState(this)), event)) ==> 
                        && f_process_event(old(toDVCNodeState(this)), event) == toDVCNodeStateAndOuputs(this)
                        && isValid();                
                case ResendAttestationShares => 
                    assert (old(isValid()) && f_process_event.requires(old(toDVCNodeState(this)), event)) ==> 
                        && f_process_event(old(toDVCNodeState(this)), event) == toDVCNodeStateAndOuputs(this)
                        && isValid();                
                case NoEvent =>
                    assert (old(isValid()) && f_process_event.requires(old(toDVCNodeState(this)), event)) ==> 
                        && f_process_event(old(toDVCNodeState(this)), event) == toDVCNodeStateAndOuputs(this)
                        && isValid();                
                    
            }            

            return Success;
        }

        method serve_attestation_duty...
        ensures (old(isValid()) && f_serve_attestation_duty.requires(old(toDVCNodeState(this)), attestation_duty)) ==> 
                && f_serve_attestation_duty(old(toDVCNodeState(this)), attestation_duty) == toDVCNodeStateAndOuputs(this)
                && isValid()
                && s.Success?
        {
            ...;
            {
                var o := toDVCNodeState(this);
                ...;
                assert o == old(toDVCNodeState(this)).(
                            attestation_duties_queue := old(toDVCNodeState(this)).attestation_duties_queue + [attestation_duty]
                        );
                assert (old(isValid()) && f_serve_attestation_duty.requires(old(toDVCNodeState(this)), attestation_duty)) ==> f_serve_attestation_duty(old(toDVCNodeState(this)), attestation_duty) == toDVCNodeStateAndOuputs(this);
            }

        }

        method check_for_next_queued_duty...
        ensures (old(isValid()) && f_check_for_next_queued_duty.requires(old(toDVCNodeState(this))))==> 
                && f_check_for_next_queued_duty(old(toDVCNodeState(this))) == toDVCNodeStateAndOuputs(this)
                && isValid()
                && s.Success?
        {
            if...
            {
                if...
                {

                    ...;
                    {
                        assert old(isValid()) ==> isValid();
                        ...;

                        assert (old(isValid()) && f_check_for_next_queued_duty.requires(old(toDVCNodeState(this)))) ==> f_check_for_next_queued_duty(old(toDVCNodeState(this))) == toDVCNodeStateAndOuputs(this);       
                    }

                }
                else if...
                {
                    ...;
                    assert (old(isValid()) && f_check_for_next_queued_duty.requires(old(toDVCNodeState(this)))) ==> f_check_for_next_queued_duty(old(toDVCNodeState(this))) == toDVCNodeStateAndOuputs(this);
                }
                else
                {
                    assert (old(isValid()) && f_check_for_next_queued_duty.requires(old(toDVCNodeState(this)))) ==> f_check_for_next_queued_duty(old(toDVCNodeState(this))) == toDVCNodeStateAndOuputs(this);
                }
            }
            else
            {
                assert (old(isValid()) && f_check_for_next_queued_duty.requires(old(toDVCNodeState(this)))) ==> f_check_for_next_queued_duty(old(toDVCNodeState(this))) == toDVCNodeStateAndOuputs(this);
            }
        }     

        method start_next_duty...
        ensures 
                old(isValid()) ==>
                (
                    && isValid()
                    && (f_start_next_duty.requires(old(toDVCNodeState(this)), attestation_duty) ==> 
                        && (f_start_next_duty(old(toDVCNodeState(this)), attestation_duty) == toDVCNodeStateAndOuputs(this))
                        && s.Success?
                    )
                )
        {
            if old(isValid())
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
            if old(isValid())
            {
                lemmaMapKeysHasOneEntryInItems(att_consensus.consensus_instances_started, attestation_duty.slot);
                                                                                     
                assert f_start_next_duty(old(toDVCNodeState(this)), attestation_duty) == toDVCNodeStateAndOuputs(this);
            }
        }

        method update_attestation_slashing_db...
        ensures f_update_attestation_slashing_db(old(toDVCNodeState(this)).attestation_slashing_db, attestation_data, attestation_duty_pubkey) == this.attestation_slashing_db;
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
        ensures (old(isValid()) && f_att_consensus_decided.requires(old(toDVCNodeState(this)), id, decided_attestation_data)) ==> 
                && f_att_consensus_decided(old(toDVCNodeState(this)), id, decided_attestation_data) == toDVCNodeStateAndOuputs(this)
                && isValid()
                && r.Success?
        {
            ...;
            {
            if old(isValid()) && f_att_consensus_decided.requires(old(toDVCNodeState(this)), id, decided_attestation_data)
            {
                var r := f_att_consensus_decided_helper(old(toDVCNodeState(this)), id, decided_attestation_data);
                var s := old(current_attesation_duty).safe_get().slot;

                forall e | e in old(toDVCNodeState(this)).attestation_consensus_engine_state.attestation_consensus_active_instances.Keys
                ensures e in r.state.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys
                {
                    lemmaMapKeysHasOneEntryInItems(old(toDVCNodeState(this)).attestation_consensus_engine_state.attestation_consensus_active_instances, e);
                }   

                assert f_att_consensus_decided_helper(old(toDVCNodeState(this)), id, decided_attestation_data).state == toDVCNodeStateAndOuputs(this).state;
            }                
                ...;
            }
            ...;
        }

        method listen_for_attestation_shares...
        ensures f_listen_for_attestation_shares(old(toDVCNodeState(this)), attestation_share) == toDVCNodeStateAndOuputs(this);
        ensures old(isValid()) ==> isValid()
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
                    // future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided
            )      

        }   

        method listen_for_new_imported_blocks...
        ensures (old(isValid()) && f_listen_for_new_imported_blocks.requires(old(toDVCNodeState(this)), block)) ==> 
                    && f_listen_for_new_imported_blocks(old(toDVCNodeState(this)), block) == toDVCNodeStateAndOuputs(this)
                    && isValid()
                    && s.Success?
        {
            assert (old(isValid()) && f_listen_for_new_imported_blocks.requires(old(toDVCNodeState(this)), block)) ==> block.body.state_root in bn.state_roots_of_imported_blocks;
            ...;
            while...
                invariant 0 <= i <= |block.body.attestations|
                invariant  old(isValid()) ==> isValid();                 
                invariant block.body.state_root in bn.state_roots_of_imported_blocks;
                invariant (isValid() && block.body.state_root in old(bn.state_roots_of_imported_blocks)) ==>
                    att_consensus_instances_already_decided == 
                    old(future_att_consensus_instances_already_decided) + listen_for_new_imported_blocks_helper(old(toDVCNodeState(this)), block, valIndex, i); 
                    
                invariant isValid() ==> toDVCNodeState(this) == old(toDVCNodeState(this))
                invariant toDVCNodeStateAndOuputs(this).outputs == getEmptyOuputs();   
            {

            }

            var o1 := toDVCNodeState(this);
            ...;
        

            if...
            {
                var o2 := toDVCNodeState(this);
                assert (old(isValid()) && f_listen_for_new_imported_blocks.requires(old(toDVCNodeState(this)), block)) ==>
            toDVCNodeState(this) == listen_for_new_imported_blocks_helper_2(old(toDVCNodeState(this)), block);    
                ...;
                assert old(isValid()) ==> isValid();
            }
            else
            {
                var o2 := toDVCNodeState(this);
                assert (old(isValid()) && f_listen_for_new_imported_blocks.requires(old(toDVCNodeState(this)), block)) ==>
            toDVCNodeState(this) == listen_for_new_imported_blocks_helper_2(old(toDVCNodeState(this)), block);    
                ...;
                assert old(isValid()) ==> isValid();            
            }
        }

        method resend_attestation_share...
        ensures old(isValid()) ==>
                                && isValid()
                                && f_resend_attestation_share(old(toDVCNodeState(this))) == toDVCNodeStateAndOuputs(this)
        {
            ...;
            assert  old(isValid()) ==> f_resend_attestation_share(old(toDVCNodeState(this))).state == toDVCNodeStateAndOuputs(this).state;
            var setWithRecipient := set att_share | att_share in attestation_shares_to_broadcast.Values :: addRecepientsToMessage(att_share, peers);
            var setWithRecipientFlattened := setUnion(setWithRecipient);
            assert old(isValid()) ==>network.att_shares_sent == old(network.att_shares_sent) +[setWithRecipientFlattened];                
            assert old(isValid()) ==>seqMinusToSet(network.att_shares_sent, old(network.att_shares_sent)) == {setWithRecipientFlattened};
            assert  old(isValid()) ==>toDVCNodeStateAndOuputs(this).outputs.att_shares_sent == setWithRecipientFlattened;
            assert  old(isValid()) ==>f_resend_attestation_share(old(toDVCNodeState(this))) == toDVCNodeStateAndOuputs(this);                  
        }
    }
}