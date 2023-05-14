include "../../../common/commons.dfy"
include "../../../specs/dvc/dvc_attestation_creation.dfy"
include "../../../specs/dvc/consensus_engine.dfy"
include "../../bn_axioms.dfy"
include "../../rs_axioms.dfy"


module Att_DVC_Spec {
    import opened Types 
    import opened Common_Functions
    import opened Set_Seq_Helper
    import opened Signing_Methods
    import Att_DVC_Spec_NonInstr
    import opened BN_Axioms
    import opened RS_Axioms
    import opened Consensus_Engine_Instr
    
    datatype Att_DVCState = Att_DVCState(
        current_attestation_duty: Optional<AttestationDuty>,
        latest_attestation_duty: Optional<AttestationDuty>,
        attestation_slashing_db: set<SlashingDBAttestation>,
        rcvd_attestation_shares: map<Slot,map<(AttestationData, seq<bool>), set<AttestationShare>>>,
        attestation_shares_to_broadcast: map<Slot, AttestationShare>,
        attestation_consensus_engine_state: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>,
        peers: set<BLSPubkey>,
        construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>,
        // TODO: Note difference with spec.py
        dv_pubkey: BLSPubkey,
        future_att_consensus_instances_already_decided:  map<Slot, AttestationData>,
        bn: BNState<Attestation>,
        rs: RSState,
        
        ghost all_rcvd_duties: set<AttestationDuty>
    )

    datatype Att_DVCStateAndOuputs = Att_DVCStateAndOuputs(
        state: Att_DVCState,
        outputs: AttestationOutputs
    )

    predicate Init(
        s: Att_DVCState,
        dv_pubkey: BLSPubkey,
        peers: set<BLSPubkey>,
        construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>,
        initial_attestation_slashing_db: set<SlashingDBAttestation>,
        rs_pubkey: BLSPubkey
    )
    {
        s == Att_DVCState(
            current_attestation_duty := None,
            latest_attestation_duty := None,
            attestation_slashing_db := initial_attestation_slashing_db,
            rcvd_attestation_shares := map[],
            attestation_shares_to_broadcast := map[],                                                  
            attestation_consensus_engine_state := getInitialAttConsensusEngineState(),
            peers := peers,
            construct_signed_attestation_signature := construct_signed_attestation_signature,
            dv_pubkey := dv_pubkey,
            future_att_consensus_instances_already_decided := map[],
            bn := s.bn,
            rs := RSState(pubkey := rs_pubkey),
            all_rcvd_duties := {}
        )
    }

    predicate Next(
        s: Att_DVCState,
        event: AttestationEvent,
        s': Att_DVCState,
        outputs: AttestationOutputs
    )
    requires f_process_event.requires(s, event)
    {
        var newNodeStateAndOutputs := Att_DVCStateAndOuputs(
            state := s',
            outputs := outputs
        );

        && f_process_event(s, event ) == newNodeStateAndOutputs
    }

    function f_process_event(
        s: Att_DVCState,
        event: AttestationEvent
    ): Att_DVCStateAndOuputs
    requires
            match event 
            case ServeAttestationDuty(attestation_duty) => 
                && f_serve_attestation_duty.requires(s, attestation_duty)
            case AttConsensusDecided(id, decided_attestation_data) => 
                && f_att_consensus_decided.requires(s, id,  decided_attestation_data)
            case ReceivedAttestationShare(attestation_share) => 
                f_listen_for_attestation_shares.requires(s, attestation_share)
            case ImportedNewBlock(block) => 
                f_listen_for_new_imported_blocks.requires(s, block)
            case ResendAttestationShares => 
                f_resend_attestation_share.requires(s) 
            case NoEvent => 
                true
    {
        match event 
            case ServeAttestationDuty(attestation_duty) => 
                f_serve_attestation_duty(s, attestation_duty)
            case AttConsensusDecided(id, decided_attestation_data) => 
                f_att_consensus_decided(s, id,  decided_attestation_data)
            case ReceivedAttestationShare(attestation_share) => 
                f_listen_for_attestation_shares(s, attestation_share)
            case ImportedNewBlock(block) => 
                f_listen_for_new_imported_blocks(s, block)
            case ResendAttestationShares => 
                f_resend_attestation_share(s)
            case NoEvent => 
                Att_DVCStateAndOuputs(state := s, outputs := getEmptyAttestationOuputs() )
    }    

    // Wraps a Att_DVC state with outputs to construct a state with type Att_DVCStateAndOutputs
    function f_wrap_Att_DVCState_with_Outputs(
        dvc: Att_DVCState,
        outputs: AttestationOutputs
    ): (ret: Att_DVCStateAndOuputs)
    ensures ret.state == dvc
    {
        Att_DVCStateAndOuputs(
                state := dvc,
                outputs := outputs
            )
    }  

    function f_serve_attestation_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty
    ): Att_DVCStateAndOuputs    
    requires attestation_duty.slot !in process.attestation_consensus_engine_state.active_consensus_instances.Keys
    requires || !process.latest_attestation_duty.isPresent()
             || process.latest_attestation_duty.safe_get().slot < attestation_duty.slot
    requires attestation_duty.slot !in process.attestation_consensus_engine_state.active_consensus_instances.Keys
    {
        var process_rcvd_duty := 
                process.(all_rcvd_duties := process.all_rcvd_duties + {attestation_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_attestation_duty(process_rcvd_duty);
        f_check_for_next_duty(
            process_after_stopping_active_consensus_instance,
            attestation_duty
        )
    }    

    function f_terminate_current_attestation_duty(
        process: Att_DVCState
    ): (ret_process: Att_DVCState)
    ensures !ret_process.current_attestation_duty.isPresent()
    {
        // There exists an active consensus instance for the current attestation duty.
        // In other words, a process has not know a decision for the current attestation duty.
        if process.current_attestation_duty.isPresent()
        then 
            var process_after_stopping_active_consensus_instance :=
                    process.(
                        current_attestation_duty := None
                    );                    
            process_after_stopping_active_consensus_instance
        // Either a process did not receive any attestation duty before
        // or it knew a decision for the last attestation duty.
        else 
            process
    } 

    function f_check_for_next_duty(
        process: Att_DVCState,
        attestation_duty: AttestationDuty
    ): Att_DVCStateAndOuputs
    requires !process.current_attestation_duty.isPresent()
    requires attestation_duty.slot !in process.attestation_consensus_engine_state.active_consensus_instances.Keys
    requires || !process.latest_attestation_duty.isPresent()
             || process.latest_attestation_duty.safe_get().slot < attestation_duty.slot
    {
        if attestation_duty.slot in process.future_att_consensus_instances_already_decided.Keys 
        then
            var new_attestation_slashing_db := 
                    f_update_attestation_slashing_db(
                        process.attestation_slashing_db, 
                        process.future_att_consensus_instances_already_decided[attestation_duty.slot]
                    );
            var new_process := 
                    process.(
                        current_attestation_duty := None,
                        latest_attestation_duty := Some(attestation_duty),
                        future_att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided - {attestation_duty.slot},
                        attestation_slashing_db := new_attestation_slashing_db,
                        attestation_consensus_engine_state := updateAttConsensusInstanceValidityCheck(
                            process.attestation_consensus_engine_state,
                            new_attestation_slashing_db
                        )                        
                    );
            f_wrap_Att_DVCState_with_Outputs(new_process, getEmptyAttestationOuputs())
        else
            f_start_next_duty(process, attestation_duty)
    }         

    function f_start_next_duty(process: Att_DVCState, attestation_duty: AttestationDuty): Att_DVCStateAndOuputs
    requires attestation_duty.slot !in process.attestation_consensus_engine_state.active_consensus_instances.Keys
    requires || !process.latest_attestation_duty.isPresent()
             || process.latest_attestation_duty.safe_get().slot < attestation_duty.slot
    {
        var new_process := 
                process.(
                            current_attestation_duty := Some(attestation_duty),
                            latest_attestation_duty := Some(attestation_duty),
                            attestation_consensus_engine_state := startAttConsensusInstance(
                                process.attestation_consensus_engine_state,
                                attestation_duty.slot,
                                attestation_duty,
                                process.attestation_slashing_db
                            )
                );
        f_wrap_Att_DVCState_with_Outputs(new_process, getEmptyAttestationOuputs())     
    }      

    function get_aggregation_bits(
        index: nat
    ): seq<bool>
    {
        seq(index, i => if i + 1 == index then true else false)
    } 

    function f_update_attestation_slashing_db(
        attestation_slashing_db: set<SlashingDBAttestation>, 
        attestation_data: AttestationData
    ): (new_attestation_slashing_db: set<SlashingDBAttestation>)   
    ensures && var slashing_db_attestation := SlashingDBAttestation(
                                            source_epoch := attestation_data.source.epoch,
                                            target_epoch := attestation_data.target.epoch,
                                            signing_root := Some(hash_tree_root(attestation_data)));
            && new_attestation_slashing_db == attestation_slashing_db + {slashing_db_attestation}
    {
        var slashing_db_attestation := SlashingDBAttestation(
                                            source_epoch := attestation_data.source.epoch,
                                            target_epoch := attestation_data.target.epoch,
                                            signing_root := Some(hash_tree_root(attestation_data)));
        
        attestation_slashing_db + {slashing_db_attestation}
    }    

    function f_calc_att_with_sign_share_from_decided_att_data(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData
    ): (att_share: AttestationShare)
    requires process.current_attestation_duty.isPresent()
    {
        var local_current_attestation_duty := process.current_attestation_duty.safe_get();
        var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
        var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
        var attestation_signature_share := rs_sign_attestation(decided_attestation_data, fork_version, attestation_signing_root, process.rs);
        var attestation_with_signature_share := AttestationShare(
                    aggregation_bits := get_aggregation_bits(local_current_attestation_duty.validator_index),
                    data := decided_attestation_data, 
                    signature := attestation_signature_share
                ); 

        attestation_with_signature_share
    }  

    function f_update_att_slashing_db_and_consensus_engine_after_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData,
        attestation_with_signature_share: AttestationShare,
        new_attestation_slashing_db: set<SlashingDBAttestation>
    ): (process': Att_DVCState)
    requires process.current_attestation_duty.isPresent()
    requires id == process.current_attestation_duty.safe_get().slot
    ensures process'.attestation_slashing_db == new_attestation_slashing_db
    {
        var local_current_attestation_duty := process.current_attestation_duty.safe_get();

        var ret_process := 
                process.(
                    current_attestation_duty := None,
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                    attestation_slashing_db := new_attestation_slashing_db,
                    attestation_consensus_engine_state := updateAttConsensusInstanceValidityCheck(
                        process.attestation_consensus_engine_state,
                        new_attestation_slashing_db
                    )
                );
        
        ret_process
    }

    function f_att_consensus_decided(
        process: Att_DVCState,
        id: Slot,
        decided_attestation_data: AttestationData
    ): Att_DVCStateAndOuputs
    {
        if  && process.current_attestation_duty.isPresent()
            && id == process.current_attestation_duty.safe_get().slot
            && id == decided_attestation_data.slot
        then

            var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);

            var attestation_with_signature_share := f_calc_att_with_sign_share_from_decided_att_data(
                                                        process,
                                                        id,
                                                        decided_attestation_data
                                                    );       
            var process_mod := 
                    f_update_att_slashing_db_and_consensus_engine_after_att_consensus_decided(
                            process,
                            id,
                            decided_attestation_data,
                            attestation_with_signature_share,
                            new_attestation_slashing_db
                        );           

            var outputs := getEmptyAttestationOuputs().(
                                    att_shares_sent := multicast(attestation_with_signature_share, process.peers)
                                );
             
            f_wrap_Att_DVCState_with_Outputs(process_mod, outputs)     
        else 
            f_wrap_Att_DVCState_with_Outputs(process, getEmptyAttestationOuputs())               
    }    

    function f_listen_for_attestation_shares(
        process: Att_DVCState,
        attestation_share: AttestationShare
    ): Att_DVCStateAndOuputs
    {
        var activate_att_consensus_intances := process.attestation_consensus_engine_state.active_consensus_instances.Keys;

        if 
            || (activate_att_consensus_intances == {} && !process.latest_attestation_duty.isPresent())
            || (activate_att_consensus_intances != {} && minInSet(activate_att_consensus_intances) <= attestation_share.data.slot)
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

                var process_with_new_att_shares_db := 
                        process.(
                            rcvd_attestation_shares := new_attestation_shares_db
                        );

                            
                if process_with_new_att_shares_db.construct_signed_attestation_signature(process_with_new_att_shares_db.rcvd_attestation_shares[attestation_share.data.slot][k]).isPresent() 
                then
                    var aggregated_attestation := 
                        f_construct_aggregated_attestation_for_new_attestation_share(
                            attestation_share,
                            k, 
                            process_with_new_att_shares_db.construct_signed_attestation_signature,
                            process_with_new_att_shares_db.rcvd_attestation_shares
                        );

                    var new_outputs := getEmptyAttestationOuputs().(
                                                submitted_data := {aggregated_attestation} 
                                            );

                    var process_after_submitting_attestations := 
                        process_with_new_att_shares_db.(
                            bn := process_with_new_att_shares_db.bn.(
                                submitted_data := process_with_new_att_shares_db.bn.submitted_data + [aggregated_attestation]
                            )
                        );

                    f_wrap_Att_DVCState_with_Outputs(process_after_submitting_attestations, new_outputs)
                else 
                    f_wrap_Att_DVCState_with_Outputs(process, getEmptyAttestationOuputs())  
        else
            f_wrap_Att_DVCState_with_Outputs(process, getEmptyAttestationOuputs())          
    }

    function f_listen_for_new_imported_blocks_helper_1(
        process: Att_DVCState,
        block: BeaconBlock
    ): map<Slot, AttestationData>
    requires block.body.state_root in process.bn.state_roots_of_imported_blocks
    requires    var valIndex := bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);
                forall a1, a2 | 
                        && a1 in block.body.attestations
                        && Att_DVC_Spec_NonInstr.isMyAttestation(a1, process.bn, block, valIndex)
                        && a2 in block.body.attestations
                        && Att_DVC_Spec_NonInstr.isMyAttestation(a2, process.bn, block, valIndex)                        
                    ::
                        a1.data.slot == a2.data.slot ==> a1 == a2    
    {
        var valIndex := bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);
        map a |
                && a in block.body.attestations
                && Att_DVC_Spec_NonInstr.isMyAttestation(a, process.bn, block, valIndex)
                && ( || !process.latest_attestation_duty.isPresent()
                     || ( && process.latest_attestation_duty.isPresent() 
                          && process.latest_attestation_duty.safe_get().slot < a.data.slot ) )
            ::
                a.data.slot := a.data        
    }

    function f_listen_for_new_imported_blocks_helper_2(
        process: Att_DVCState,
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
        process: Att_DVCState,
        block: BeaconBlock
    ): Att_DVCStateAndOuputs
    requires block.body.state_root in process.bn.state_roots_of_imported_blocks
    requires    var valIndex := bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);
                forall a1, a2 | 
                        && a1 in block.body.attestations
                        && Att_DVC_Spec_NonInstr.isMyAttestation(a1, process.bn, block, valIndex)
                        && a2 in block.body.attestations
                        && Att_DVC_Spec_NonInstr.isMyAttestation(a2, process.bn, block, valIndex)                        
                    ::
                        a1.data.slot == a2.data.slot ==> a1 == a2
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
                f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var process_after_stopping_consensus_instance :=
                process.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopAttConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );                    

        if process_after_stopping_consensus_instance.current_attestation_duty.isPresent() && process_after_stopping_consensus_instance.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided then
            var decided_attestation_data := att_consensus_instances_already_decided[process_after_stopping_consensus_instance.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(process_after_stopping_consensus_instance.attestation_slashing_db, decided_attestation_data);
            var process_after_updating_validity_check := process_after_stopping_consensus_instance.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateAttConsensusInstanceValidityCheck(
                    process_after_stopping_consensus_instance.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )
            );
            f_wrap_Att_DVCState_with_Outputs(process_after_updating_validity_check, getEmptyAttestationOuputs()) 
        else
            f_wrap_Att_DVCState_with_Outputs(process, getEmptyAttestationOuputs())   
    }    
  
    function f_resend_attestation_share(
        process: Att_DVCState
    ): Att_DVCStateAndOuputs
    {
        var new_outputs := getEmptyAttestationOuputs().(
                                    att_shares_sent :=
                                        multicast_multiple(process.attestation_shares_to_broadcast.Values, process.peers)
                                );
        f_wrap_Att_DVCState_with_Outputs(process, new_outputs) 
    }        

    // Is node n the owner of a given attestation share att
    predicate is_owner_of_att_share(att_share: AttestationShare, dvc: Att_DVCState)
    {
        && var data := att_share.data;
        && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(data.target.epoch));
        && var att_signing_root := compute_attestation_signing_root(data, fork_version);
        && var att_share_signature := rs_sign_attestation(data, fork_version, att_signing_root, dvc.rs);        
        && att_share_signature == att_share.signature
    }
}
