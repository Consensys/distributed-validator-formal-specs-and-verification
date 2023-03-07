include "../../../common/block_proposer/block_types.dfy"
include "../../../common/block_proposer/block_common_functions.dfy"
include "../../../common/block_proposer/block_signing_functions.dfy"
include "../../../specs/dvc/dvc_block_proposer.dfy"
include "block_dvc_spec_axioms.dfy"


module DVC_Spec {
    import opened Block_Types 
    import opened Block_Common_Functions
    import opened Block_Signing_Functions
    import Block_DVC_Spec_NonInstr
    import opened Block_DVC_Spec_Axioms


    datatype BlockConsensusEngineState = BlockConsensusEngineState(
        active_block_consensus_instances: map<Slot, BlockConsensusValidityCheckState>,
        ghost block_slashing_db_hist: map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>>
    )

    function getInitialBlockConensusEngineState(): BlockConsensusEngineState
    {
        BlockConsensusEngineState(
            active_block_consensus_instances := map[],
            block_slashing_db_hist := map[]
        )
    }

    function startBlockConsensusInstance(
        s: BlockConsensusEngineState,
        slot: Slot,
        proposer_duty: ProposerDuty,
        block_slashing_db: set<SlashingDBBlock>,
        complete_signed_randao_reveal: BLSSignature
    ): BlockConsensusEngineState
    requires slot !in s.active_block_consensus_instances.Keys    
    requires slot == proposer_duty.slot
    {
        var bcvc := 
            BlockConsensusValidityCheckState(
                    proposer_duty := proposer_duty,
                    complete_signed_randao_reveal := complete_signed_randao_reveal,
                    validityPredicate := (block: BeaconBlock) => consensus_is_valid_beacon_block(
                                                                    block_slashing_db, 
                                                                    block, 
                                                                    proposer_duty,
                                                                    complete_signed_randao_reveal)
            );
        
        assert (bcvc.validityPredicate == ((block: BeaconBlock) => consensus_is_valid_beacon_block(
                                                                    block_slashing_db, 
                                                                    block, 
                                                                    bcvc.proposer_duty,
                                                                    bcvc.complete_signed_randao_reveal)));                
        
        var new_active_block_consensus_instances := 
            s.active_block_consensus_instances[
                slot := bcvc
            ];

        s.(
            active_block_consensus_instances := new_active_block_consensus_instances,
            block_slashing_db_hist := 
                addToBlockSlashingDBHist(
                    s.block_slashing_db_hist,
                    slot,
                    bcvc.validityPredicate,
                    block_slashing_db                    
                )
                
        )
    }

    function addToBlockSlashingDBHist(
        hist: map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>>,
        id: Slot,
        vp: BeaconBlock -> bool,
        block_slashing_db: set<SlashingDBBlock>
    ): (new_hist: map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>>)
    ensures hist.Keys + { id } == new_hist.Keys
    ensures ( forall slot0, vp0 ::
                    && var hist_slot0 := getOrDefault(hist, slot0, map[]);
                    && var hist_slot_vp0 := getOrDefault(hist_slot0, vp0, {});
                    && var new_hist_slot0 := getOrDefault(new_hist, slot0, map[]);
                    && var new_hist_slot_vp0 := getOrDefault(new_hist_slot0, vp0, {});
                    && (( slot0 != id || vp0 != vp )
                        ==> 
                        hist_slot_vp0 == new_hist_slot_vp0
                        )
                    && ((slot0 == id && vp0 == vp )
                        ==> 
                        hist_slot_vp0 + {block_slashing_db} == new_hist_slot_vp0
                        )
            )
    {
        var hist_id := getOrDefault(hist, id, map[]);
        var new_hist_id_vp := getOrDefault(hist_id, vp, {}) + {block_slashing_db};
        hist[
            id := hist_id[
                vp := new_hist_id_vp
            ]
        ]
    }  


    function stopBlockConsensusInstances(
        s: BlockConsensusEngineState,
        ids: set<Slot>
    ): BlockConsensusEngineState
    {
        s.(
            active_block_consensus_instances := s.active_block_consensus_instances - ids
        )
    }    
 
    function updateBlockSlashingDBHist(
        hist: map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>>,
        new_active_block_consensus_instances : map<Slot, BlockConsensusValidityCheckState>,
        new_block_slashing_db: set<SlashingDBBlock>
    ): (new_hist: map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>>)
    ensures hist.Keys + new_active_block_consensus_instances.Keys == new_hist.Keys
    {
            var ret 
                := map k: Slot | k in (new_active_block_consensus_instances.Keys + hist.Keys)
                    ::            
                    if k in new_active_block_consensus_instances.Keys then 
                        var vp := new_active_block_consensus_instances[k].validityPredicate;
                        var hist_k := getOrDefault(hist, k, map[]);
                        var hist_k_vp := getOrDefault(hist_k, vp, {}) + {new_block_slashing_db};
                        hist_k[
                            vp := hist_k_vp
                        ]
                    else
                        hist[k];
            ret
    }

    function updateBlockConsensusInstanceValidityCheckHelper(
        m: map<Slot, BlockConsensusValidityCheckState>,
        new_block_slashing_db: set<SlashingDBBlock>
    ): (r: map<Slot, BlockConsensusValidityCheckState>)
    ensures r.Keys <= m.Keys
    {
            map it | it in m.Items
                ::
                it.0 := it.1.(
                    validityPredicate := (block: BeaconBlock) => consensus_is_valid_beacon_block(
                                                                    new_block_slashing_db, 
                                                                    block, 
                                                                    it.1.proposer_duty,
                                                                    it.1.complete_signed_randao_reveal 
                                                                 )
                )        
    } 

    function updateBlockConsensusInstanceValidityCheck(
        s: BlockConsensusEngineState,
        new_block_slashing_db: set<SlashingDBBlock>
    ): (r: BlockConsensusEngineState)
    {
        s.(
            active_block_consensus_instances := 
                updateBlockConsensusInstanceValidityCheckHelper(
                    s.active_block_consensus_instances,
                    new_block_slashing_db
                )
        )
    }


    datatype DVCState = DVCState(
        current_proposer_duty: Optional<ProposerDuty>,
        last_served_proposer_duty: Optional<ProposerDuty>,
        block_slashing_db: set<SlashingDBBlock>,
        block_share_db: BlockSignatureShareDB,        
        rcvd_randao_shares: map<Slot, set<RandaoShare>>,
        rcvd_block_shares: map<Slot, map<BeaconBlock, set<SignedBeaconBlock>>>,
        construct_signed_randao_reveal: (set<BLSSignature>) -> Optional<BLSSignature>,
        construct_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>,
        block_shares_to_broadcast: map<Slot, SignedBeaconBlock>, 
        randao_shares_to_broadcast: map<Slot, RandaoShare>,
        peers: set<BLSPubkey>,        
        // TODO: Note difference with spec.py
        dv_pubkey: BLSPubkey,
        future_decided_slots: map<Slot, BeaconBlock>,
        bn: BNState,
        rs: RSState,
        block_consensus_engine_state: BlockConsensusEngineState,
        
        ghost all_rcvd_duties: set<ProposerDuty>
    )

    type Outputs = Block_DVC_Spec_NonInstr.Outputs

    function getEmptyOuputs(): Outputs
    {
        Block_DVC_Spec_NonInstr.Outputs(
            {},
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

    datatype DVCStateAndOuputs = DVCStateAndOuputs(
        state: DVCState,
        outputs: Outputs
    )

    predicate Init(
        s: DVCState,         
        dv_pubkey: BLSPubkey,
        peers: set<BLSPubkey>,                    
        construct_signed_randao_reveal: (set<BLSSignature>) -> Optional<BLSSignature>,
        construct_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>,        
        initial_block_slashing_db: set<SlashingDBBlock>,
        rs_pubkey: BLSPubkey
    )
    {
        s == DVCState(
            // proposer_duty_queue := [],
            future_decided_slots := map[],
            block_shares_to_broadcast := map[],
            randao_shares_to_broadcast := map[],
            block_slashing_db := initial_block_slashing_db,
            block_share_db := map[],
            rcvd_randao_shares := map[],
            rcvd_block_shares := map[],
            current_proposer_duty := None,
            last_served_proposer_duty := None,
            bn := s.bn,
            rs := Block_DVC_Spec_NonInstr.getInitialRS(rs_pubkey),
            dv_pubkey := dv_pubkey,
            peers := peers,                        
            construct_signed_block := construct_signed_block,
            construct_signed_randao_reveal := construct_signed_randao_reveal,
            block_consensus_engine_state := getInitialBlockConensusEngineState(),
            all_rcvd_duties := {}
        )
    }

    // predicate Next(
    //     s: DVCState,
    //     event: Event,
    //     s': DVCState,
    //     outputs: Outputs
    // )
    // {
    //     var newNodeStateAndOutputs := DVCStateAndOuputs(
    //         state := s',
    //         outputs := outputs
    //     );

    //     newNodeStateAndOutputs == f_process_event(s, event)
    // }

    // function f_process_event(
    //     s: DVCState,
    //     event: Event
    // ): DVCStateAndOuputs
    // requires
    //         match event 
    //         case ServeAttstationDuty(proposer_duty) => 
    //             && f_serve_proposer_duty.requires(s, proposer_duty)
    //         case AttConsensusDecided(id, decided_block_data) => 
    //             && f_block_consensus_decided.requires(s, id,  decided_block_data)
    //         case ReceivedAttestationShare(block_share) => 
    //             f_listen_for_block_shares.requires(s, block_share)
    //         case ImportedNewBlock(block) => 
    //             f_listen_for_new_imported_blocks.requires(s, block)
    //         case ResendAttestationShares => 
    //             f_resend_block_share.requires(s) 
    //         case NoEvent => 
    //             true
    // {
    //     match event 
    //         case ServeAttstationDuty(proposer_duty) => 
    //             f_serve_proposer_duty(s, proposer_duty)
    //         case AttConsensusDecided(id, decided_block_data) => 
    //             f_block_consensus_decided(s, id,  decided_block_data)
    //         case ReceivedAttestationShare(block_share) => 
    //             f_listen_for_block_shares(s, block_share)
    //         case ImportedNewBlock(block) => 
    //             f_listen_for_new_imported_blocks(s, block)
    //         case ResendAttestationShares => 
    //             f_resend_block_share(s)
    //         case NoEvent => 
    //             DVCStateAndOuputs(state := s, outputs := getEmptyOuputs() )
    // }  

    function merge_two_outputs(
        outputs1: Outputs,
        outputs2: Outputs
    ): Outputs
    {
        getEmptyOuputs().(
            block_shares_sent := outputs1.block_shares_sent + outputs2.block_shares_sent,
            randao_shares_sent := outputs1.randao_shares_sent + outputs2.randao_shares_sent,
            submitted_signed_blocks := outputs1.submitted_signed_blocks + outputs2.submitted_signed_blocks
        )
    }  

    // Wraps a DVC state with outputs to construct a state with type DVCStateAndOutputs
    function f_wrap_DVCState_with_Outputs(
        dvc: DVCState,
        outputs: Outputs
    ): (ret: DVCStateAndOuputs)
    ensures ret.state == dvc
    {
        DVCStateAndOuputs(
                state := dvc,
                outputs := outputs
            )
    }  

    function f_terminate_current_proposer_duty(
        process: DVCState
    ): (ret_process: DVCState)
    ensures !ret_process.current_proposer_duty.isPresent()
    {
        // There exists an active consensus instance for the current proposer duty.
        // In other words, a process has not know a decision for the current proposer duty.
        if process.current_proposer_duty.isPresent()
        then 
            var process_after_terminating_current_duty :=
                    process.(
                        current_proposer_duty := None
                    );                    
            process_after_terminating_current_duty
        // Either a process did not receive any proposer duty before
        // or it knew a decision for the last proposer duty.
        else 
            process
    }  

    function f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty
    ): DVCStateAndOuputs 
    {   
        var process_after_stopping_active_consensus_instance := f_terminate_current_proposer_duty(process);

        f_broadcast_randao_share(
            process_after_stopping_active_consensus_instance,
            proposer_duty
        )        
    }

    function f_broadcast_randao_share(
        process: DVCState,
        serving_duty: ProposerDuty
    ): DVCStateAndOuputs 
    {
        var slot := serving_duty.slot;
        var epoch := compute_epoch_at_slot(slot);            
        var fork_version := bn_get_fork_version(slot);    
        var root := compute_randao_reveal_signing_root(slot);
        var randao_signature := rs_sign_randao_reveal(slot, fork_version, root, process.rs);                                                           
        var randao_share := RandaoShare(serving_duty, epoch, slot, root, randao_signature);        
        var broadcasted_output := 
            getEmptyOuputs().(
                randao_shares_sent := multicast(randao_share, process.peers)                                            
            );
        
        var process_after_checking_for_next_duty := 
            f_check_for_next_duty(
                process.(
                    randao_shares_to_broadcast := process.randao_shares_to_broadcast[serving_duty.slot := randao_share]
                ),
                serving_duty
            );
        
        var merged_outputs := merge_two_outputs(broadcasted_output, process_after_checking_for_next_duty.outputs);

        f_wrap_DVCState_with_Outputs(
            process_after_checking_for_next_duty.state,
            merged_outputs
        )
    }
  
    function f_check_for_next_duty(
        process: DVCState,
        serving_duty: ProposerDuty
    ): DVCStateAndOuputs 
    {            
        var slot := serving_duty.slot;
        if slot in process.future_decided_slots 
        then        
            var block := process.future_decided_slots[slot];                
            var process_with_updated_slashing_db := f_update_block_slashing_db(process, block);            
            var process_after_removing_slot
                := 
                process_with_updated_slashing_db.(                        
                    future_decided_slots := process.future_decided_slots - {slot}
                );

            f_wrap_DVCState_with_Outputs(
                process_after_removing_slot,
                getEmptyOuputs()
            )    
        else 
            var process_after_adding_new_duty := 
                process.(
                    current_proposer_duty := Some(serving_duty),
                    last_served_proposer_duty := Some(serving_duty)
                );

            f_start_consensus_if_can_construct_randao_share(
                process_after_adding_new_duty
            )                    
    }

    function f_start_consensus_if_can_construct_randao_share(
        process: DVCState
    ): DVCStateAndOuputs
    {        
        if && process.current_proposer_duty.isPresent()
           && process.current_proposer_duty.safe_get().slot in process.rcvd_randao_shares
        then
            var proposer_duty := process.current_proposer_duty.safe_get();
            var all_rcvd_randao_sig := 
                    set randao_share | randao_share in process.rcvd_randao_shares[
                                                process.current_proposer_duty.safe_get().slot]
                                                    :: randao_share.signature;                
            var constructed_randao_reveal := process.construct_signed_randao_reveal(all_rcvd_randao_sig);
            if && constructed_randao_reveal.isPresent()  
               && proposer_duty.slot !in process.block_consensus_engine_state.active_block_consensus_instances.Keys 
            then                      
                var validityPredicate := ((block: BeaconBlock)  => 
                                            consensus_is_valid_beacon_block(
                                                process.block_slashing_db, 
                                                block, 
                                                process.current_proposer_duty.safe_get(),
                                                constructed_randao_reveal.safe_get()));        
                DVCStateAndOuputs(
                    state :=  process.(
                        block_consensus_engine_state := startBlockConsensusInstance(
                            process.block_consensus_engine_state,
                            proposer_duty.slot,
                            proposer_duty,
                            process.block_slashing_db,
                            constructed_randao_reveal.safe_get()
                        )
                    ),
                    outputs := getEmptyOuputs()
                )                        
            else 
                f_wrap_DVCState_with_Outputs(
                    process,
                    getEmptyOuputs()
                )
        else
            f_wrap_DVCState_with_Outputs(
                    process,
                    getEmptyOuputs()
            )
    }
    
    function f_update_block_slashing_db(
        process: DVCState,        
        block: BeaconBlock
    ): DVCState
    {   
        var newDBBlock := SlashingDBBlock(block.slot, hash_tree_root(block));        
        process.(                 
            block_slashing_db := process.block_slashing_db + {newDBBlock}        
        )
    }       
    
    function f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock
    ): DVCStateAndOuputs
    {
        if  && process.current_proposer_duty.isPresent()
            && id == process.current_proposer_duty.safe_get().slot
            && id == block.slot
        then
            var process_with_updated_slashing_db := f_update_block_slashing_db(process, block);
            var block_signing_root := compute_block_signing_root(block);
            var fork_version := bn_get_fork_version(block.slot);
            var block_signature := rs_sign_block(block, fork_version, block_signing_root, process.rs);
            var block_share := SignedBeaconBlock(block, block_signature);
            var slot := block.slot;
            var process_after_broadcasting_block_share := process.(                
                    block_shares_to_broadcast := process.block_shares_to_broadcast[slot := block_share]
                );
            var multicastOutputs := getEmptyOuputs().(
                                        block_shares_sent := multicast(block_share, process.peers)
                                    );

            f_wrap_DVCState_with_Outputs(
                process_after_broadcasting_block_share,
                merge_two_outputs(multicastOutputs, getEmptyOuputs())
            )   
        else 
            f_wrap_DVCState_with_Outputs(process, getEmptyOuputs())               
    }    

    predicate is_slot_for_current_or_future_instances(
        process: DVCState,        
        received_slot: Slot
    )    
    {
        // TODO: The check below is not consistent with the clean-up operation done in
        // listen_for_new_imported_blocks. Here, any share for future slot is accepted, whereas
        // listen_for_new_imported_blocks cleans up the received shares for any already-decided slot. This
        // inconsistency should be fixed up by either accepting here only shares with slot higher than the
        // maximum already-decided slot or changing the clean-up code in listen_for_new_imported_blocks to clean
        // up only slot lower thant the slot of the current/latest duty.
        var active_block_consensus_instances := 
            process.block_consensus_engine_state.active_block_consensus_instances.Keys;

        || (active_block_consensus_instances == {} && !process.last_served_proposer_duty.isPresent())
        || (active_block_consensus_instances != {} && get_min(active_block_consensus_instances) <= received_slot)
        || (active_block_consensus_instances == {} && !process.current_proposer_duty.isPresent() && process.last_served_proposer_duty.isPresent() && process.last_served_proposer_duty.safe_get().slot < received_slot)            
    }

    function f_listen_for_block_share(
        process: DVCState,
        block_share: SignedBeaconBlock
    ): DVCStateAndOuputs
    {
        var slot := block_share.message.slot;

        if is_slot_for_current_or_future_instances(process, slot) then
            var data := block_share.message;
            var rcvd_block_shares_db_at_slot := getOrDefault(process.rcvd_block_shares, slot, map[]);
            var process_with_new_block_share :=
                process.(
                    rcvd_block_shares := 
                        process.rcvd_block_shares[
                            slot := 
                                rcvd_block_shares_db_at_slot[
                                    data := 
                                        getOrDefault(rcvd_block_shares_db_at_slot, data, {}) + 
                                        {block_share}
                                    ]
                        ]
                );            
            if process.construct_signed_block(process_with_new_block_share.rcvd_block_shares[slot][data]).isPresent() then                
                    var complete_signed_block := process.construct_signed_block(process_with_new_block_share.rcvd_block_shares[slot][data]).safe_get();                      
                    f_wrap_DVCState_with_Outputs(
                        process_with_new_block_share,
                        getEmptyOuputs().(
                                submitted_signed_blocks := {complete_signed_block}
                            )
                    )
            else 
                f_wrap_DVCState_with_Outputs(
                    process,
                    getEmptyOuputs()
                )            
        else
            f_wrap_DVCState_with_Outputs(
                process,
                getEmptyOuputs()
            )     
    }

    function f_listen_for_randao_share(
        process: DVCState,
        randao_share: RandaoShare
    ): DVCStateAndOuputs         
    {
        var slot := randao_share.slot;
        var active_block_consensus_instances := process.block_consensus_engine_state.active_block_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        then
            var process_with_dlv_randao_share := 
                    process.(
                        rcvd_randao_shares := process.rcvd_randao_shares[slot := getOrDefault(process.rcvd_randao_shares, slot, {}) + 
                                                                                        {randao_share} ]
                    );     
            f_start_consensus_if_can_construct_randao_share(
                process_with_dlv_randao_share
            )
        else
            f_wrap_DVCState_with_Outputs(
                process,
                getEmptyOuputs()
            )
    }   

    
    function f_listen_for_new_imported_block(
        process: DVCState,
        signed_block: SignedBeaconBlock
    ): DVCStateAndOuputs
    {        
        var block_consensus_already_decided := 
            if verify_bls_signature(signed_block.message, signed_block.signature, process.dv_pubkey) then
                process.future_decided_slots[
                    signed_block.message.slot := signed_block.message
                ]
            else 
                process.future_decided_slots
            ;

        var new_block_consensus_engine_state := stopBlockConsensusInstances(
                                                    process.block_consensus_engine_state,
                                                    block_consensus_already_decided.Keys
                                                );

        var cleaned_up_process := 
            process.(
                block_shares_to_broadcast := process.block_shares_to_broadcast - block_consensus_already_decided.Keys,
                rcvd_block_shares := process.rcvd_block_shares - block_consensus_already_decided.Keys,
                randao_shares_to_broadcast := process.randao_shares_to_broadcast - block_consensus_already_decided.Keys,
                rcvd_randao_shares := process.rcvd_randao_shares - block_consensus_already_decided.Keys,
                block_consensus_engine_state := new_block_consensus_engine_state
            );

        var process_with_new_future_decided_slots :=
            if cleaned_up_process.last_served_proposer_duty.isPresent() then
                var slot := cleaned_up_process.last_served_proposer_duty.safe_get().slot;
                var old_instances := set i | 
                                        && i in block_consensus_already_decided 
                                        && i <= cleaned_up_process.last_served_proposer_duty.safe_get().slot;
                cleaned_up_process.(
                    future_decided_slots := block_consensus_already_decided - old_instances
                )                      
            else
                cleaned_up_process.(
                    future_decided_slots := block_consensus_already_decided
                )
            ;

        if && process_with_new_future_decided_slots.current_proposer_duty.isPresent() 
           && process_with_new_future_decided_slots.current_proposer_duty.safe_get().slot in block_consensus_already_decided.Keys
        then
            var process_with_new_slashing_db := 
                f_update_block_slashing_db(
                    process_with_new_future_decided_slots,
                    block_consensus_already_decided[
                        process_with_new_future_decided_slots.current_proposer_duty.safe_get().slot
                    ]
                );
            var process_without_current_duty := process_with_new_future_decided_slots.(
                                                current_proposer_duty := None
                                            );
            
            f_wrap_DVCState_with_Outputs(
                process_without_current_duty,
                getEmptyOuputs()
            )
        else
            f_wrap_DVCState_with_Outputs(
                process_with_new_future_decided_slots,
                getEmptyOuputs()
            )
    }
  
    function f_resend_block_share(
        process: DVCState
    ): DVCStateAndOuputs
    {
        DVCStateAndOuputs(
            state := process,
            outputs := getEmptyOuputs().(
                block_shares_sent :=
                    if process.block_shares_to_broadcast.Keys != {} then
                        multicast_multiple(process.block_shares_to_broadcast.Values, process.peers)                        
                    else
                        {}
                    )
        )
    }    

    function f_resend_randao_share(
        process: DVCState
    ): DVCStateAndOuputs
    {
        DVCStateAndOuputs(
            state := process,
            outputs := getEmptyOuputs().(
                randao_shares_sent :=
                    if process.randao_shares_to_broadcast.Keys != {} then
                        multicast_multiple(process.randao_shares_to_broadcast.Values, process.peers)                        
                    else
                        {}
                    )
        )
    }      
}

