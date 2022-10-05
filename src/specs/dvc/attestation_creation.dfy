include "../../common/commons.dfy"
include "../../dvc_implementation/attestation_creation.dfy"
include "../../proofs/no_slashable_attestations/common/dvc_spec_axioms.dfy"


module DVCNode_Spec_NonInstr {
    import opened Types 
    import opened CommonFunctions
    import opened DVCNode_Externs
    import opened DVCNode_Spec_Axioms


    datatype AttestationConsensusValidityCheckState = AttestationConsensusValidityCheckState(
        attestation_duty: AttestationDuty,
        validityPredicate: AttestationData -> bool
    )

    datatype ConsensusEngineState = ConsensusEngineState(
        attestation_consensus_active_instances: map<Slot, AttestationConsensusValidityCheckState>
    )

    function getInitialConensusEngineState(): ConsensusEngineState
    {
        ConsensusEngineState(
            attestation_consensus_active_instances := map[]
        )
    }

    function startConsensusInstance(
        s: ConsensusEngineState,
        id: Slot,
        attestation_duty: AttestationDuty,
        attestation_slashing_db: set<SlashingDBAttestation>
    ): ConsensusEngineState
    requires id !in s.attestation_consensus_active_instances.Keys
    {
        var acvc := AttestationConsensusValidityCheckState(
                    attestation_duty := attestation_duty,
                    validityPredicate := (ad: AttestationData) => consensus_is_valid_attestation_data(attestation_slashing_db, ad, attestation_duty)
                );
        
        assert (acvc.validityPredicate == (ad: AttestationData) => consensus_is_valid_attestation_data(attestation_slashing_db, ad, acvc.attestation_duty));
        var new_attestation_consensus_active_instances := s.attestation_consensus_active_instances[
                id := acvc
            ];
        s.(
            attestation_consensus_active_instances := new_attestation_consensus_active_instances
        )
    }

    function addToAttSlashingDBHist(
        hist: map<Slot, map<AttestationData -> bool, set<set<SlashingDBAttestation>>>>,
        id: Slot,
        vp: AttestationData -> bool,
        new_attestation_slashing_db: set<SlashingDBAttestation>
    ): (new_hist: map<Slot, map<AttestationData -> bool, set<set<SlashingDBAttestation>>>>)
    {

            var  hist_id := getOrDefault(hist, id, map[]);
            var new_hist_id_vp := getOrDefault(hist_id, vp, {}) + {new_attestation_slashing_db};
            hist[
                id := hist_id[
                    vp := new_hist_id_vp
                ]
            ]
    }  


    function stopConsensusInstances(
        s: ConsensusEngineState,
        ids: set<Slot>
    ): ConsensusEngineState
    {
        s.(
            attestation_consensus_active_instances := s.attestation_consensus_active_instances - ids
        )
    }    


    function updateConsensusInstanceValidityCheckHelper(
        m: map<Slot, AttestationConsensusValidityCheckState>,
        new_attestation_slashing_db: set<SlashingDBAttestation>
    ): (r: map<Slot, AttestationConsensusValidityCheckState>)
    // Questions: It seems r.Keys == m.Keys, not <=
    ensures r.Keys <= m.Keys
    {
            map it | it in m.Items
                ::
                it.0 := it.1.(
                    validityPredicate := (ad: AttestationData) => consensus_is_valid_attestation_data(new_attestation_slashing_db, ad, it.1.attestation_duty)
                )        
    }

  
    function updateAttSlashingDBHist(
        hist: map<Slot, map<AttestationData -> bool, set<set<SlashingDBAttestation>>>>,
        new_attestation_consensus_active_instances : map<Slot, AttestationConsensusValidityCheckState>,
        new_attestation_slashing_db: set<SlashingDBAttestation>
    ): (new_hist: map<Slot, map<AttestationData -> bool, set<set<SlashingDBAttestation>>>>)
    {
            var ret 
                := map k: Slot | k in (new_attestation_consensus_active_instances.Keys + hist.Keys)
                    ::            
                    if k in new_attestation_consensus_active_instances.Keys then 
                        var vp := new_attestation_consensus_active_instances[k].validityPredicate;
                        var hist_k := getOrDefault(hist, k, map[]);
                        var hist_k_vp := getOrDefault(hist_k, vp, {}) + {new_attestation_slashing_db};
                        hist_k[
                            vp := hist_k_vp
                        ]
                    else
                        hist[k];
            ret
    }

    function updateConsensusInstanceValidityCheck(
        s: ConsensusEngineState,
        new_attestation_slashing_db: set<SlashingDBAttestation>
    ): (r: ConsensusEngineState)
    {
        var new_attestation_consensus_active_instances := updateConsensusInstanceValidityCheckHelper(
                    s.attestation_consensus_active_instances,
                    new_attestation_slashing_db
                );
        s.(
            attestation_consensus_active_instances := new_attestation_consensus_active_instances
        )
    }

    function getInitialRS(
        pubkey: BLSPubkey
    ): RSState
    {
        RSState(
            pubkey := pubkey
        )
    }  

    datatype DVCNodeState = DVCNodeState(
        current_attestation_duty: Optional<AttestationDuty>,
        latest_attestation_duty: Optional<AttestationDuty>,
        attestation_duties_queue: seq<AttestationDuty>,
        attestation_slashing_db: set<SlashingDBAttestation>,
        rcvd_attestation_shares: map<Slot,map<(AttestationData, seq<bool>), set<AttestationShare>>>,
        attestation_shares_to_broadcast: map<Slot, AttestationShare>,
        attestation_consensus_engine_state: ConsensusEngineState,
        peers: set<BLSPubkey>,
        construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>,
        // TODO: Note difference with spec.py
        dv_pubkey: BLSPubkey,
        future_att_consensus_instances_already_decided:  map<Slot, AttestationData>,
        bn: BNState,
        rs: RSState
    )

    datatype Outputs = Outputs(
        att_shares_sent: set<MessaageWithRecipient<AttestationShare>>,
        attestations_submitted: set<Attestation>
    )    

    function getEmptyOuputs(): Outputs
    {
        Outputs(
            {},
            {}
        )
    }  


    function multicast<M>(m: M, receipients: set<BLSPubkey>): set<MessaageWithRecipient<M>>
    {
        addRecepientsToMessage(m, receipients)
    }

    function multicast_multiple<M>(ms: set<M>, receipients: set<BLSPubkey>): set<MessaageWithRecipient<M>>
    {
        var setWithRecipient := set m | m in ms :: addRecepientsToMessage(m, receipients);
        setUnion(setWithRecipient)
    }    

    datatype DVCNodeStateAndOuputs = DVCNodeStateAndOuputs(
        state: DVCNodeState,
        outputs: Outputs
    )

    predicate Init(
        s: DVCNodeState,
        dv_pubkey: BLSPubkey,
        peers: set<BLSPubkey>,
        construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>,
        initial_attestation_slashing_db: set<SlashingDBAttestation>,
        rs_pubkey: BLSPubkey
    )
    {
        s == DVCNodeState(
            current_attestation_duty := None,
            latest_attestation_duty := None,
            attestation_duties_queue := [],
            attestation_slashing_db := initial_attestation_slashing_db,
            rcvd_attestation_shares := map[],
            attestation_shares_to_broadcast := map[],
            attestation_consensus_engine_state := getInitialConensusEngineState(),
            peers := peers,
            construct_signed_attestation_signature := construct_signed_attestation_signature,
            dv_pubkey := dv_pubkey,
            future_att_consensus_instances_already_decided := map[],
            bn := s.bn,
            rs := getInitialRS(rs_pubkey)
        )
    }

    predicate Next(
        s: DVCNodeState,
        event: Event,
        s': DVCNodeState,
        outputs: Outputs
    )
    {
        var newNodeStateAndOutputs := DVCNodeStateAndOuputs(
            state := s',
            outputs := outputs
        );

        && f_process_event.requires(s, event)
        && f_process_event(s, event ) == newNodeStateAndOutputs
    }

    function f_process_event(
        s: DVCNodeState,
        event: Event
    ): DVCNodeStateAndOuputs
    requires
            match event 
            case ServeAttstationDuty(attestation_duty) => 
                && f_serve_attestation_duty.requires(s, attestation_duty)
            case AttConsensusDecided(id, decided_attestation_data) => 
                && f_att_consensus_decided.requires(s, id,  decided_attestation_data)
            case ReceviedAttesttionShare(attestation_share) => 
                f_listen_for_attestation_shares.requires(s, attestation_share)
            case ImportedNewBlock(block) => 
                f_listen_for_new_imported_blocks.requires(s, block)
            case ResendAttestationShares => 
                f_resend_attestation_share.requires(s) 
            case NoEvent => 
                true
    {
        match event 
            case ServeAttstationDuty(attestation_duty) => 
                f_serve_attestation_duty(s, attestation_duty)
            case AttConsensusDecided(id, decided_attestation_data) => 
                f_att_consensus_decided(s, id,  decided_attestation_data)
            case ReceviedAttesttionShare(attestation_share) => 
                f_listen_for_attestation_shares(s, attestation_share)
            case ImportedNewBlock(block) => 
                f_listen_for_new_imported_blocks(s, block)
            case ResendAttestationShares => 
                f_resend_attestation_share(s)
            case NoEvent => 
                DVCNodeStateAndOuputs(state := s, outputs := getEmptyOuputs() )
    }    

    function f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty
    ): DVCNodeStateAndOuputs
    requires forall ad | ad in process.attestation_duties_queue + [attestation_duty]:: ad.slot !in process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys
    {
        f_check_for_next_queued_duty(
            process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty]
            )
        )
    }    

    function f_check_for_next_queued_duty(process: DVCNodeState): DVCNodeStateAndOuputs
    requires forall ad | ad in process.attestation_duties_queue :: ad.slot !in process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys
    decreases process.attestation_duties_queue
    {
        if  && process.attestation_duties_queue != [] 
            && (
                || process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided
                || !process.current_attestation_duty.isPresent()
            )    
        then
            
                if process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided.Keys then
                    var queue_head := process.attestation_duties_queue[0];
                    var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, process.future_att_consensus_instances_already_decided[queue_head.slot]);
                    f_check_for_next_queued_duty(process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..],
                        future_att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided - {queue_head.slot},
                        attestation_slashing_db := new_attestation_slashing_db,
                        attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                            process.attestation_consensus_engine_state,
                            new_attestation_slashing_db
                        )                        
                    ))
                else
                    var new_process := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    );         
                    f_start_next_duty(new_process, process.attestation_duties_queue[0])
                
        else 
            DVCNodeStateAndOuputs(
                state := process,
                outputs := getEmptyOuputs()
            )

    }         

    function f_start_next_duty(process: DVCNodeState, attestation_duty: AttestationDuty): DVCNodeStateAndOuputs
    requires attestation_duty.slot !in process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys
    {
        DVCNodeStateAndOuputs(
            state :=  process.(
                        current_attestation_duty := Some(attestation_duty),
                        latest_attestation_duty := Some(attestation_duty),
                        attestation_consensus_engine_state := startConsensusInstance(
                            process.attestation_consensus_engine_state,
                            attestation_duty.slot,
                            attestation_duty,
                            process.attestation_slashing_db
                        )
            ),
            outputs := getEmptyOuputs()
        )        
    }      

    function get_aggregation_bits(
        index: nat
    ): seq<bool>
    {
        seq(index, i => if i + 1 == index then true else false)
    } 

    function f_update_attestation_slashing_db(attestation_slashing_db: set<SlashingDBAttestation>, attestation_data: AttestationData): set<SlashingDBAttestation>     
    {
        var slashing_db_attestation := SlashingDBAttestation(
                                            source_epoch := attestation_data.source.epoch,
                                            target_epoch := attestation_data.target.epoch,
                                            signing_root := Some(hash_tree_root(attestation_data)));
        
        attestation_slashing_db + {slashing_db_attestation}
    }      

    function f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData
    ): DVCNodeStateAndOuputs
    requires forall ad | ad in process.attestation_duties_queue :: ad.slot !in process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys    
    {
        if  && process.current_attestation_duty.isPresent()
            && id == process.current_attestation_duty.safe_get().slot then

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

            var process := 
                process.(
                    current_attestation_duty := None,
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                    attestation_slashing_db := attestation_slashing_db,
                    attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                        process.attestation_consensus_engine_state,
                        attestation_slashing_db
                    )
                );

            var ret_check_for_next_queued_duty := f_check_for_next_queued_duty(process);

            ret_check_for_next_queued_duty.(
                state := ret_check_for_next_queued_duty.state,
                outputs := getEmptyOuputs().(
                    att_shares_sent := multicast(attestation_with_signature_share, process.peers)
                )          
            )        
        else 
            DVCNodeStateAndOuputs(
                state := process,
                outputs := getEmptyOuputs()
            )               
    }    

    function f_listen_for_attestation_shares(
        process: DVCNodeState,
        attestation_share: AttestationShare
    ): DVCNodeStateAndOuputs
    {
        var activate_att_consensus_intances := process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys;

        if 
            || (activate_att_consensus_intances == {} && !process.latest_attestation_duty.isPresent())
            || (activate_att_consensus_intances != {} && minSet(activate_att_consensus_intances) <= attestation_share.data.slot)
            || (activate_att_consensus_intances == {} && process.current_attestation_duty.isPresent() && process.current_attestation_duty.safe_get().slot <= attestation_share.data.slot)                
            || (activate_att_consensus_intances == {} && !process.current_attestation_duty.isPresent() && process.latest_attestation_duty.isPresent() && process.latest_attestation_duty.safe_get().slot < attestation_share.data.slot) then

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

                var process := process.(
                    rcvd_attestation_shares := new_attestation_shares_db
                );

                            
                if process.construct_signed_attestation_signature(process.rcvd_attestation_shares[attestation_share.data.slot][k]).isPresent() then
                
                    var aggregated_attestation := 
                            Attestation(
                                aggregation_bits := attestation_share.aggregation_bits,
                                data := attestation_share.data,
                                signature := process.construct_signed_attestation_signature(process.rcvd_attestation_shares[attestation_share.data.slot][k]).safe_get()
                            );

                    DVCNodeStateAndOuputs(
                        state := process.(
                            bn := process.bn.(
                                attestations_submitted := process.bn.attestations_submitted + [aggregated_attestation]
                            )
                        ),
                        outputs := getEmptyOuputs()
                        .(
                            attestations_submitted := {aggregated_attestation} 
                        )
                    ) 
                else 
                    DVCNodeStateAndOuputs(
                        state := process,
                        outputs := getEmptyOuputs()
                    ) 
        else
            DVCNodeStateAndOuputs(
                state := process,
                outputs := getEmptyOuputs()
            )         
    }
 
    predicate isMyAttestation(
        a: Attestation,
        bn: BNState,
        block: BeaconBlock,
        valIndex: Optional<ValidatorIndex>
    )
    requires block.body.state_root in bn.state_roots_of_imported_blocks
    {
            && var committee := bn_get_epoch_committees(bn, block.body.state_root, a.data.index);
            && valIndex.Some?
            && valIndex.v in committee
            && var i:nat :| i < |committee| && committee[i] == valIndex.v;
            && i < |a.aggregation_bits|
            && a.aggregation_bits[i]         
    }

    function f_listen_for_new_imported_blocks_compute_att_consensus_instances_already_decided(
        process: DVCNodeState,
        block: BeaconBlock,
        valIndex: Optional<ValidatorIndex>,
        att_consensus_instances_already_decided: map<Slot, AttestationData>,
        i: nat := 0
    ): map<Slot, AttestationData>
    requires i <= |block.body.attestations|
    requires block.body.state_root in process.bn.state_roots_of_imported_blocks
    decreases |block.body.attestations| - i
    {
        var attestations := block.body.attestations;
        if |attestations| == i then 
            att_consensus_instances_already_decided
        else
            var a := attestations[i];
            var new_att_consensus_instances_already_decided := 
                if isMyAttestation(a, process.bn, block, valIndex) then
                    att_consensus_instances_already_decided[a.data.slot := a.data]
                else
                    att_consensus_instances_already_decided
                ;
            f_listen_for_new_imported_blocks_compute_att_consensus_instances_already_decided( process, block, valIndex, new_att_consensus_instances_already_decided, i + 1)
    }

    function f_listen_for_new_imported_blocks_helper_1(
        process: DVCNodeState,
        block: BeaconBlock
    ): map<Slot, AttestationData>
    requires block.body.state_root in process.bn.state_roots_of_imported_blocks
    requires    var valIndex := bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);
                forall a1, a2 | 
                        && a1 in block.body.attestations
                        && isMyAttestation(a1, process.bn, block, valIndex)
                        && a2 in block.body.attestations
                        && isMyAttestation(a2, process.bn, block, valIndex)                        
                    ::
                        a1.data.slot == a2.data.slot ==> a1 == a2    
    {
        var valIndex := bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);
        map a |
                && a in block.body.attestations
                && isMyAttestation(a, process.bn, block, valIndex)
            ::
                a.data.slot := a.data        
    }

    function f_listen_for_new_imported_blocks_helper_2(
        process: DVCNodeState,
        att_consensus_instances_already_decided: map<Slot, AttestationData>
    ): map<int, AttestationData>
    {
        if process.latest_attestation_duty.isPresent() then
            var old_instances := 
                    set i | 
                        && i in att_consensus_instances_already_decided.Keys
                        && i <= process.latest_attestation_duty.safe_get().slot
                    ;
            att_consensus_instances_already_decided - old_instances
        else
            att_consensus_instances_already_decided     
    }

    function f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock
    ): DVCNodeStateAndOuputs
    requires block.body.state_root in process.bn.state_roots_of_imported_blocks
    requires    var valIndex := bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);
                forall a1, a2 | 
                        && a1 in block.body.attestations
                        && isMyAttestation(a1, process.bn, block, valIndex)
                        && a2 in block.body.attestations
                        && isMyAttestation(a2, process.bn, block, valIndex)                        
                    ::
                        a1.data.slot == a2.data.slot ==> a1 == a2
    requires forall ad | ad in process.attestation_duties_queue :: ad.slot !in process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var process :=
                process.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );                    

        if process.current_attestation_duty.isPresent() && process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided then
            // Stop(current_attestation_duty.safe_get().slot);
            var decided_attestation_data := att_consensus_instances_already_decided[process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);
            var process := process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    process.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );
            f_check_for_next_queued_duty(process)
        else
            DVCNodeStateAndOuputs(
                state := process,
                outputs := getEmptyOuputs()
            )
    }    
  
    function f_resend_attestation_share(
        process: DVCNodeState
    ): DVCNodeStateAndOuputs
    {
        DVCNodeStateAndOuputs(
            state := process,
            outputs := getEmptyOuputs().(
                att_shares_sent :=
                    multicast_multiple(process.attestation_shares_to_broadcast.Values, process.peers)
            )
        )

    }        

    // Is node n the owner of a given attestation share att
    predicate is_owner_of_att_share(att_share: AttestationShare, dvc: DVCNodeState)
    {
        && var data := att_share.data;
        && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(data.target.epoch));
        && var att_signing_root := compute_attestation_signing_root(data, fork_version);
        && var att_share_signature := rs_sign_attestation(data, fork_version, att_signing_root, dvc.rs);        
        && att_share_signature == att_share.signature
    }
}

module DVCNode_Externs_Proofs refines DVCNode_Externs
{
    import opened DVCNode_Spec_NonInstr
    import opened DVCNode_Spec_Axioms

    function toBNState(bn: BeaconNode): BNState
    reads bn
    {
        BNState(
            state_roots_of_imported_blocks := bn.state_roots_of_imported_blocks,
            attestations_submitted := bn.attestations_submitted
        )
    }

    trait BeaconNode...
    {
        method get_fork_version...
        ensures bn_get_fork_version(s) == v

        method get_validator_index...
        ensures state_id in this.state_roots_of_imported_blocks ==> bn_get_validator_index(toBNState(this),state_id, validator_id) == vi

        method get_epoch_committees...
        ensures state_id in this.state_roots_of_imported_blocks ==> bn_get_epoch_committees(toBNState(this), state_id, index) == sv
    }


    trait RemoteSigner...
    {
        method sign_attestation...
        ensures rs_sign_attestation(attestation_data, fork_version, signing_root, toRSState(this)) == s
    }

    function toRSState(
        rs: RemoteSigner
    ): RSState
    reads rs 
    {
        RSState(
            pubkey := rs.pubkey
        )
    }

}