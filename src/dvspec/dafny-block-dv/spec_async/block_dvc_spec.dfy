include "../utils/block_common_functions.dfy"
include "../utils/block_signing_functions.dfy"
include "../utils/block_types.dfy"
include "../impl/block_externs.dfy"


module BlockDVCNodeSpec {
    import opened BlockTypes 
    import opened BlockCommonFunctions
    import opened BlockSigningFunctions    
    import opened Block_DVC_Externs

    function {:axiom} bn_get_fork_version(slot: Slot): Version

    function {:axiom} bn_get_validator_index(bnState: BNState, state_id: Root, validator_id: BLSPubkey): (vi: Optional<ValidatorIndex>)
    requires state_id in bnState.state_roots_of_imported_blocks

    function {:axiom} bn_get_epoch_committees(bnState: BNState, state_id: Root, index: CommitteeIndex): (sv: seq<ValidatorIndex>) 
    requires state_id in bnState.state_roots_of_imported_blocks   

    // Don't need to use fork_version
    function {:axiom} rs_sign_randao_reveal(        
        slot: Slot, 
        fork_version: Version,
        signing_root: Root,
        rs: RSState
    ): BLSSignature
    requires signing_root == compute_randao_reveal_signing_root(slot)

    // Don't need to use fork_version
    function {:axiom} rs_sign_block(        
        block: BeaconBlock,
        fork_version: Version,
        signing_root: Root,
        rs: RSState
    ): BLSSignature
    requires signing_root == compute_block_signing_root(block)

    datatype BNState = BNState(
        state_roots_of_imported_blocks: set<Root>   
    )

    /*
    function getInitialBN(): BNState
    {
        BNState(
            state_roots_of_imported_blocks := {}
        )
    } 
    */   

    datatype RSState = RSState(
        pubkey: BLSPubkey
    )

    function getInitialRS(
        pubkey: BLSPubkey
    ): RSState
    {
        RSState(
            pubkey := pubkey
        )
    }  

    datatype BlockConsensusValidityCheckState = BlockConsensusValidityCheckState(
        proposer_duty: ProposerDuty,
        complete_signed_randao_reveal: BLSSignature,
        validityPredicate: BeaconBlock -> bool
    )

    datatype BlockConsensusEngineState = BlockConsensusEngineState(
        block_consensus_active_instances: map<Slot, BlockConsensusValidityCheckState>
    )

    function getInitialBlockConensusEngineState(): BlockConsensusEngineState
    {
        BlockConsensusEngineState(
            block_consensus_active_instances := map[]
        )
    }

    function startBlockConsensusInstance(
        s: BlockConsensusEngineState,
        slot: Slot,
        proposer_duty: ProposerDuty,
        block_slashing_db: set<SlashingDBBlock>,
        complete_signed_randao_reveal: BLSSignature
    ): BlockConsensusEngineState
    requires slot !in s.block_consensus_active_instances.Keys    
    {
       var bcvc := BlockConsensusValidityCheckState(
                    proposer_duty := proposer_duty,
                    complete_signed_randao_reveal := complete_signed_randao_reveal,
                    validityPredicate := (block: BeaconBlock) => consensus_is_valid_block(
                                                                    block_slashing_db, 
                                                                    block, 
                                                                    proposer_duty,
                                                                    complete_signed_randao_reveal)
                );
        assert (bcvc.validityPredicate == ((block: BeaconBlock) => consensus_is_valid_block(
                                                                    block_slashing_db, 
                                                                    block, 
                                                                    bcvc.proposer_duty,
                                                                    bcvc.complete_signed_randao_reveal)));                
        s.(
            block_consensus_active_instances := s.block_consensus_active_instances[
                slot := bcvc
            ]
        )
    }

    function stopBlockConsensusInstances(
        s: BlockConsensusEngineState,
        ids: set<Slot>
    ): BlockConsensusEngineState
    {
        s.(
            block_consensus_active_instances := s.block_consensus_active_instances - ids
        )
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
                    validityPredicate := (block: BeaconBlock) => consensus_is_valid_block(
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
            block_consensus_active_instances := 
                updateBlockConsensusInstanceValidityCheckHelper(
                    s.block_consensus_active_instances,
                    new_block_slashing_db
                )
        )
    }

    datatype DVCNodeState = DVCNodeState(
        current_proposer_duty: Optional<ProposerDuty>,
        last_served_proposer_duty: Optional<ProposerDuty>,
        proposer_duty_queue: seq<ProposerDuty>,
        block_slashing_db: BlockSlashingDB,
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
        block_consensus_engine_state: BlockConsensusEngineState
    )  

    datatype Outputs = Outputs(
        block_shares_sent: set<MessaageWithRecipient<SignedBeaconBlock>>,
        randao_shares_sent: set<MessaageWithRecipient<RandaoShare>>,        
        submitted_signed_blocks: set<SignedBeaconBlock>
    )    

    function getEmptyOuputs(): Outputs
    {
        Outputs(
            {},
            {},            
            {}
        )
    }  


    function multicast<M>(m: M, receipients: set<BLSPubkey>): set<MessaageWithRecipient<M>>
    {
        addRecepientsToMessage(m, receipients)
    }

    function multicast_msgs<M>(msgs: set<M>, receipients: set<BLSPubkey>): set<MessaageWithRecipient<M>>
    {
        var setWithRecipient := set m | m in msgs :: wrapMessageWithRecipients(m, receipients);
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
        construct_signed_randao_reveal: (set<BLSSignature>) -> Optional<BLSSignature>,
        construct_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>,        
        initial_block_slashing_db: BlockSlashingDB,
        rs_pubkey: BLSPubkey
    )
    {
        s == DVCNodeState(
            proposer_duty_queue := [],
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
            rs := getInitialRS(rs_pubkey),
            dv_pubkey := dv_pubkey,
            peers := peers,                        
            construct_signed_block := construct_signed_block,
            construct_signed_randao_reveal := construct_signed_randao_reveal,
            block_consensus_engine_state := getInitialBlockConensusEngineState()
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

        newNodeStateAndOutputs == f_Next(s, event)

        /*
        match event         
            case ServeProposerDuty(proposer_duty) => 
                f_serve_proposer_duty(s, proposer_duty) == newNodeStateAndOutputs              
            case BlockConsensusDecided(block) => 
                && f_block_consensus_decided.requires(s, block)
                && f_block_consensus_decided(s, block) == newNodeStateAndOutputs                
            case ReceiveRandaoShare(randao_share) => 
                f_listen_for_randao_share(s, randao_share) == newNodeStateAndOutputs                
            case ReceiveBlockShare(block_share) => 
                f_listen_for_block_share(s, block_share) == newNodeStateAndOutputs                                
            case ImportNewBlock(block) => 
                && f_listen_for_new_imported_block.requires(s, block)
                && f_listen_for_new_imported_block(s, block) == newNodeStateAndOutputs               
            case ResendRandaoShare => 
                f_resend_randao_share(s) == newNodeStateAndOutputs                
            case ResendBlockShare => 
                f_resend_block_share(s) == newNodeStateAndOutputs                
            case NoEvent => 
                DVCNodeStateAndOuputs(state := s, outputs := getEmptyOuputs() ) == newNodeStateAndOutputs
            */
    }

    function f_Next(
        s: DVCNodeState,
        event: Event        
    ): DVCNodeStateAndOuputs
    {
        match event         
            case ServeProposerDuty(proposer_duty) => 
                f_serve_proposer_duty(s, proposer_duty)
            case BlockConsensusDecided(block) => 
                f_block_consensus_decided(s, block)
            case ReceiveRandaoShare(randao_share) => 
                f_listen_for_randao_share(s, randao_share)
            case ReceiveBlockShare(block_share) => 
                f_listen_for_block_share(s, block_share)
            case ImportNewBlock(block) => 
                f_listen_for_new_imported_block(s, block)
            case ResendRandaoShare => 
                f_resend_randao_share(s)
            case ResendBlockShare => 
                f_resend_block_share(s) 
            case NoEvent => 
                DVCNodeStateAndOuputs(state := s, outputs := getEmptyOuputs() )
    }

    function f_listen_for_new_imported_block(
        process: DVCNodeState,
        signed_block: SignedBeaconBlock
    ): DVCNodeStateAndOuputs
    // requires forall pd | pd in process.proposer_duty_queue :: pd.slot !in process.block_consensus_engine_state.block_consensus_active_instances.Keys        
    {
        if forall pd | pd in process.proposer_duty_queue :: pd.slot !in process.block_consensus_engine_state.block_consensus_active_instances.Keys 
        then
            DVCNodeStateAndOuputs(
                state := process,
                outputs := getEmptyOuputs()
            )
        else 
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
                var process_after_checking_duty_queue := f_check_for_next_queued_duty(process_without_current_duty);
                DVCNodeStateAndOuputs(
                    state := process_after_checking_duty_queue.state,
                    outputs := getEmptyOuputs()
                )
            else
                DVCNodeStateAndOuputs(
                    state := process_with_new_future_decided_slots,
                    outputs := getEmptyOuputs()
                )
    }

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

    function f_listen_for_block_share(
        process: DVCNodeState,
        block_share: SignedBeaconBlock
    ): DVCNodeStateAndOuputs
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
                    DVCNodeStateAndOuputs(
                        state := process_with_new_block_share,
                        outputs := getEmptyOuputs().(
                                submitted_signed_blocks := {complete_signed_block}
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

    function f_listen_for_randao_share(
        process: DVCNodeState,
        randao_share: RandaoShare
    ): DVCNodeStateAndOuputs         
    {
        var slot := randao_share.slot;
        var block_consensus_active_instances := process.block_consensus_engine_state.block_consensus_active_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) then
            var process_with_dlv_randao_share := 
                    process.(
                        rcvd_randao_shares := process.rcvd_randao_shares[slot := getOrDefault(process.rcvd_randao_shares, slot, {}) + 
                                                                                        {randao_share} ]
                    );     
            f_start_consensus_if_can_construct_randao_share(
                process_with_dlv_randao_share
            )
        else
            DVCNodeStateAndOuputs(
                state := process,
                outputs := getEmptyOuputs()
            )
    }       

    predicate is_slot_for_current_or_future_instances(
        process: DVCNodeState,        
        received_slot: Slot
    )    
    {
        // TODO: The check below is not consistent with the clean-up operation done in
        // listen_for_new_imported_blocks. Here, any share for future slot is accepted, whereas
        // listen_for_new_imported_blocks cleans up the received shares for any already-decided slot. This
        // inconsistency should be fixed up by either accepting here only shares with slot higher than the
        // maximum already-decided slot or changing the clean-up code in listen_for_new_imported_blocks to clean
        // up only slot lower thant the slot of the current/latest duty.
        var block_consensus_active_instances := 
            process.block_consensus_engine_state.block_consensus_active_instances.Keys;

        || (block_consensus_active_instances == {} && !process.last_served_proposer_duty.isPresent())
        || (block_consensus_active_instances != {} && get_min(block_consensus_active_instances) <= received_slot)
        || (block_consensus_active_instances == {} && process.current_proposer_duty.isPresent() && process.current_proposer_duty.safe_get().slot <= received_slot)                
        || (block_consensus_active_instances == {} && !process.current_proposer_duty.isPresent() && process.last_served_proposer_duty.isPresent() && process.last_served_proposer_duty.safe_get().slot < received_slot)            
    }

    function f_serve_proposer_duty(
        process: DVCNodeState,
        proposer_duty: ProposerDuty
    ): DVCNodeStateAndOuputs 
    {   
        f_broadcast_randao_share(
            process.(
                proposer_duty_queue := process.proposer_duty_queue + [proposer_duty]
            ),
            proposer_duty
        )        
    }

    function f_broadcast_randao_share(
        process: DVCNodeState,
        serving_duty: ProposerDuty
    ): DVCNodeStateAndOuputs 
    {
        var slot := serving_duty.slot;
        var epoch := compute_epoch_at_slot(slot);            
        var fork_version := bn_get_fork_version(slot);    
        var root := compute_randao_reveal_signing_root(slot);
        var randao_signature := rs_sign_randao_reveal(slot, fork_version, root, process.rs);                                                           
        var randao_share := RandaoShare(serving_duty, epoch, slot, root, randao_signature);        
        var broadcasted_output := getEmptyOuputs().(
                                        randao_shares_sent := multicast(randao_share, process.peers)                                            
                                    );
        var process_after_checking_duty_queue := 
            f_check_for_next_queued_duty(
                process.(
                    randao_shares_to_broadcast := process.randao_shares_to_broadcast[serving_duty.slot := randao_share]
                )
            );
        var merged_outputs := merge_two_outputs(broadcasted_output, process_after_checking_duty_queue.outputs);

        DVCNodeStateAndOuputs(
            state := process_after_checking_duty_queue.state,
            outputs := merged_outputs
        )
    }
    
    function f_check_for_next_queued_duty(
        process: DVCNodeState
    ): DVCNodeStateAndOuputs 
    decreases process.proposer_duty_queue
    {
        if process.proposer_duty_queue != [] then
            var slot := process.proposer_duty_queue[0].slot;
            if slot in process.future_decided_slots then
                
                var queue_head := process.proposer_duty_queue[0];
                var block := process.future_decided_slots[queue_head.slot];                
                var process_with_updated_slashing_db := f_update_block_slashing_db(process, block);
                f_check_for_next_queued_duty(
                    process_with_updated_slashing_db.(                        
                        proposer_duty_queue := process.proposer_duty_queue[1..],                  
                        future_decided_slots := process.future_decided_slots - {slot}
                    )                            
                )                                
            else 
                if !process.current_proposer_duty.isPresent() then
                    var queue_head := process.proposer_duty_queue[0];
                    var process_after_enqueue := process.(
                            proposer_duty_queue := process.proposer_duty_queue[1..],
                            current_proposer_duty := Some(queue_head),
                            last_served_proposer_duty := Some(queue_head)
                        );
                    f_start_consensus_if_can_construct_randao_share(
                        process_after_enqueue
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

    function f_start_consensus_if_can_construct_randao_share(
        process: DVCNodeState
    ): DVCNodeStateAndOuputs
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
               && proposer_duty.slot !in process.block_consensus_engine_state.block_consensus_active_instances.Keys 
            then                      
                var validityPredicate := ((block: BeaconBlock)  => 
                                            consensus_is_valid_block(
                                                process.block_slashing_db, 
                                                block, 
                                                process.current_proposer_duty.safe_get(),
                                                constructed_randao_reveal.safe_get()));        
                DVCNodeStateAndOuputs(
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
    
    function f_update_block_slashing_db(
        process: DVCNodeState,        
        block: BeaconBlock
    ): DVCNodeState
    {   
        var newDBBlock := SlashingDBBlock(block.slot, hash_tree_root(block));        
        process.(                 
            block_slashing_db := process.block_slashing_db + {newDBBlock}        
        )
    }

    function f_block_consensus_decided(
        process: DVCNodeState,
        block: BeaconBlock
    ): DVCNodeStateAndOuputs 
    // requires process.current_proposer_duty.isPresent()
    // requires forall pd | pd in process.proposer_duty_queue :: pd.slot !in process.block_consensus_engine_state.block_consensus_active_instances
    {
        if && process.current_proposer_duty.isPresent()
           && forall pd | pd in process.proposer_duty_queue :: pd.slot !in process.block_consensus_engine_state.block_consensus_active_instances
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
            var process_after_checking_duty_queue := f_check_for_next_queued_duty(process_after_broadcasting_block_share);

            DVCNodeStateAndOuputs(
                state := process_after_checking_duty_queue.state,
                outputs := merge_two_outputs(multicastOutputs, process_after_checking_duty_queue.outputs)
            )
        else
            DVCNodeStateAndOuputs(
                state := process,
                outputs := getEmptyOuputs()
            )
    } 

    function f_resend_block_share(
        process: DVCNodeState
    ): DVCNodeStateAndOuputs
    {
        DVCNodeStateAndOuputs(
            state := process,
            outputs := getEmptyOuputs().(
                block_shares_sent :=
                    if process.block_shares_to_broadcast.Keys != {} then
                        multicast_msgs(process.block_shares_to_broadcast.Values, process.peers)                        
                    else
                        {}
                    )
        )
    }    

    function f_resend_randao_share(
        process: DVCNodeState
    ): DVCNodeStateAndOuputs
    {
        DVCNodeStateAndOuputs(
            state := process,
            outputs := getEmptyOuputs().(
                randao_shares_sent :=
                    if process.randao_shares_to_broadcast.Keys != {} then
                        multicast_msgs(process.randao_shares_to_broadcast.Values, process.peers)                        
                    else
                        {}
                    )
        )
    }      
}