include "../../common/commons.dfy"
include "../../proofs/bn_axioms.dfy"
include "../../proofs/rs_axioms.dfy"
include "../dvc/consensus_engine.dfy"

module DVC_Block_Proposer_Spec_NonInstr {
    import opened Types 
    import opened Common_Functions
    import opened Set_Seq_Helper
    import opened Signing_Methods
    import opened Consensus_Engine_NonInstr
    import opened BN_Axioms    
    import opened RS_Axioms

    datatype DVCState = DVCState(
        current_proposer_duty: Optional<ProposerDuty>,
        latest_proposer_duty: Optional<ProposerDuty>,
        block_slashing_db: set<SlashingDBBlock>,             
        rcvd_randao_shares: map<Slot, set<RandaoShare>>,
        rcvd_block_shares: map<Slot, map<BeaconBlock, set<SignedBeaconBlock>>>,
        construct_complete_signed_randao_reveal: (set<BLSSignature>) -> Optional<BLSSignature>,
        construct_complete_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>,
        block_shares_to_broadcast: map<Slot, SignedBeaconBlock>, 
        randao_shares_to_broadcast: map<Slot, RandaoShare>,
        peers: set<BLSPubkey>,        
        // TODO: Note difference with spec.py
        dv_pubkey: BLSPubkey,
        future_consensus_instances_on_blocks_already_decided: map<Slot, BeaconBlock>,
        bn: BNState<SignedBeaconBlock>,
        rs: RSState,
        block_consensus_engine_state: ConsensusEngineState<BlockConsensusValidityCheckState>
    )

    datatype Outputs = Outputs(
        sent_block_shares: set<MessaageWithRecipient<SignedBeaconBlock>>,
        sent_randao_shares: set<MessaageWithRecipient<RandaoShare>>,        
        submitted_data: set<SignedBeaconBlock>
    )

    function getEmptyOuputs(): Outputs
    {
        Outputs(
            {},
            {},
            {}
        )
    }  

    datatype DVCStateAndOuputs = DVCStateAndOuputs(
        state: DVCState,
        outputs: Outputs
    )

    predicate Init(
        s: DVCState,         
        dv_pubkey: BLSPubkey,
        peers: set<BLSPubkey>,                    
        construct_complete_signed_randao_reveal: (set<BLSSignature>) -> Optional<BLSSignature>,
        construct_complete_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>,        
        initial_block_slashing_db: set<SlashingDBBlock>,
        rs_pubkey: BLSPubkey
    )
    requires && s.bn.state_roots_of_imported_blocks == {}
             && s.bn.submitted_data == []
    {
        s == DVCState(
            // proposer_duty_queue := [],
            future_consensus_instances_on_blocks_already_decided := map[],
            block_shares_to_broadcast := map[],
            randao_shares_to_broadcast := map[],
            block_slashing_db := initial_block_slashing_db,            
            rcvd_randao_shares := map[],
            rcvd_block_shares := map[],
            current_proposer_duty := None,
            latest_proposer_duty := None,
            bn := s.bn,
            rs := RSState(pubkey := rs_pubkey),
            dv_pubkey := dv_pubkey,
            peers := peers,                        
            construct_complete_signed_block := construct_complete_signed_block,
            construct_complete_signed_randao_reveal := construct_complete_signed_randao_reveal,
            block_consensus_engine_state := getInitialBlockConensusEngineState()
        )
    }

    predicate Next(
        s: DVCState,
        event: BlockEvent,
        s': DVCState,
        outputs: Outputs
    )
    {
        &&  var newNodeStateAndOutputs := 
                DVCStateAndOuputs(
                    state := s',
                    outputs := outputs
                );
        && f_process_event.requires(s, event)
        && newNodeStateAndOutputs == f_process_event(s, event)
    }

    function f_process_event(
        s: DVCState,
        event: BlockEvent        
    ): DVCStateAndOuputs
    requires match event         
                case ServeProposerDuty(proposer_duty) => 
                    && f_serve_proposer_duty.requires(s, proposer_duty)
                case BlockConsensusDecided(id, block) => 
                    && f_block_consensus_decided.requires(s, id, block)
                case ReceiveRandaoShare(randao_share) => 
                    && f_listen_for_randao_shares.requires(s, randao_share)
                case ReceiveSignedBeaconBlock(block_share) => 
                    && f_listen_for_block_signature_shares.requires(s, block_share)
                case ImportedNewBlock(block) => 
                    && f_listen_for_new_imported_blocks.requires(s, block)
                case ResendRandaoRevealSignatureShare => 
                    && f_resend_randao_share.requires(s)
                case ResendBlockShare => 
                    && f_resend_block_share.requires(s) 
                case NoEvent => 
                    true
    {
        match event         
            case ServeProposerDuty(proposer_duty) => 
                f_serve_proposer_duty(s, proposer_duty)
            case BlockConsensusDecided(id, block) => 
                f_block_consensus_decided(s, id, block)
            case ReceiveRandaoShare(randao_share) => 
                f_listen_for_randao_shares(s, randao_share)
            case ReceiveSignedBeaconBlock(block_share) => 
                f_listen_for_block_signature_shares(s, block_share)
            case ImportedNewBlock(block) => 
                f_listen_for_new_imported_blocks(s, block)
            case ResendRandaoRevealSignatureShare => 
                f_resend_randao_share(s)
            case ResendBlockShare => 
                f_resend_block_share(s) 
            case NoEvent => 
                DVCStateAndOuputs(state := s, outputs := getEmptyOuputs() )
    }

    function merge_two_outputs(
        outputs1: Outputs,
        outputs2: Outputs
    ): Outputs
    {
        getEmptyOuputs().(
            sent_block_shares := outputs1.sent_block_shares + outputs2.sent_block_shares,
            sent_randao_shares := outputs1.sent_randao_shares + outputs2.sent_randao_shares,
            submitted_data := outputs1.submitted_data + outputs2.submitted_data
        )
    }

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

    function f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty
    ): DVCStateAndOuputs 
    {   
        var process_after_receiving_duty := 
            process.(
                current_proposer_duty := Some(proposer_duty),
                latest_proposer_duty := Some(proposer_duty)
            );

        // Note: It seems that we can optimize the protocol by checking whether the decision for a corresponding consensus instance
        // has been made before a node broadcasts randao shares.
        // Before other nodes alreay know the decision.
        f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty
        )        
    }

    function f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty
    ): DVCStateAndOuputs 
    requires process.latest_proposer_duty.isPresent()
    {
        var slot := proposer_duty.slot;
        var fork_version := bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
        var randao_share := 
            RandaoShare(
                proposer_duty := proposer_duty,
                slot := slot,
                signing_root := randao_reveal_signing_root,
                signature := randao_reveal_signature_share
            );
        var broadcasted_output := 
            getEmptyOuputs().(
                sent_randao_shares := multicast(randao_share, process.peers)                                            
            );
        
        var process_after_checking_for_next_duty := 
            f_check_for_next_duty(
                process.(
                    randao_shares_to_broadcast := process.randao_shares_to_broadcast[proposer_duty.slot := randao_share]
                ),
                proposer_duty
            );
        
        var merged_outputs := merge_two_outputs(broadcasted_output, process_after_checking_for_next_duty.outputs);

        DVCStateAndOuputs(
            state := process_after_checking_for_next_duty.state,
            outputs := merged_outputs
        )
    }

    function f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty
    ): DVCStateAndOuputs 
    requires process.latest_proposer_duty.isPresent()
    {            
        var slot := proposer_duty.slot;
        if slot in process.future_consensus_instances_on_blocks_already_decided.Keys
        then        
            var block := process.future_consensus_instances_on_blocks_already_decided[slot];                
            var new_block_slashing_db := 
                f_update_block_slashing_db(process.block_slashing_db, block);            
            var new_process
                := 
                process.(
                    current_proposer_duty := None,                    
                    future_consensus_instances_on_blocks_already_decided := process.future_consensus_instances_on_blocks_already_decided - {slot},
                    block_slashing_db := new_block_slashing_db,
                    block_consensus_engine_state := updateBlockConsensusInstanceValidityCheck(
                            process.block_consensus_engine_state,
                            new_block_slashing_db
                    )     
                );

            DVCStateAndOuputs(
                state := new_process,
                outputs := getEmptyOuputs()
            )    
        else 
            f_start_consensus_if_can_construct_randao_share(
                process
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
            var constructed_randao_reveal := process.construct_complete_signed_randao_reveal(all_rcvd_randao_sig);
            if && constructed_randao_reveal.isPresent()  
               && proposer_duty.slot !in process.block_consensus_engine_state.active_consensus_instances.Keys 
            then                      
                var validityPredicate := ((block: BeaconBlock)  => 
                                            ci_decision_is_valid_beacon_block(
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
                DVCStateAndOuputs(
                    state := process,
                    outputs := getEmptyOuputs()
                )
        else
            DVCStateAndOuputs(
                state := process,
                outputs := getEmptyOuputs()
            )
    }
    
    function f_update_block_slashing_db(
        block_slashing_db: set<SlashingDBBlock>,
        block: BeaconBlock
    ): (new_block_slashing_db: set<SlashingDBBlock>)
    ensures && var new_slashingDB_block := construct_SlashingDBBlock_from_beacon_block(block);        
            && block_slashing_db + {new_slashingDB_block} == new_block_slashing_db
            && new_slashingDB_block.slot == block.slot
    {   
        var new_slashingDB_block := construct_SlashingDBBlock_from_beacon_block(block);        
        block_slashing_db + {new_slashingDB_block}                
    }

    function f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock
    ): DVCStateAndOuputs
    {
        if && process.current_proposer_duty.isPresent()
           && process.current_proposer_duty.safe_get().slot == block.slot
           && id == block.slot
        then
            var new_block_slashing_db := f_update_block_slashing_db(process.block_slashing_db, block);
            var block_signing_root := compute_block_signing_root(block);
            var fork_version := bn_get_fork_version(block.slot);
            var block_signature := rs_sign_block(block, fork_version, block_signing_root, process.rs);
            var block_share := SignedBeaconBlock(block, block_signature);
            var slot := block.slot;
            var process_after_updating_block_shares_to_broadcast := process.(                
                    block_shares_to_broadcast := process.block_shares_to_broadcast[slot := block_share],
                    block_slashing_db := new_block_slashing_db,
                    block_consensus_engine_state := updateBlockConsensusInstanceValidityCheck(
                        process.block_consensus_engine_state,
                        new_block_slashing_db
                    )
                );
            var multicastOutputs := getEmptyOuputs().(
                                        sent_block_shares := multicast(block_share, process.peers)
                                    );

            DVCStateAndOuputs(
                state := process_after_updating_block_shares_to_broadcast,
                outputs := merge_two_outputs(multicastOutputs, getEmptyOuputs())
            )
        else
            DVCStateAndOuputs(
                state := process,
                outputs := getEmptyOuputs()
            )
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
        var active_consensus_instances := 
            process.block_consensus_engine_state.active_consensus_instances.Keys;

        || (active_consensus_instances == {} && !process.latest_proposer_duty.isPresent())
        || (active_consensus_instances != {} && get_min(active_consensus_instances) <= received_slot)
        || (active_consensus_instances == {} && !process.current_proposer_duty.isPresent() && process.latest_proposer_duty.isPresent() && process.latest_proposer_duty.safe_get().slot < received_slot)            
    }

    function f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock
    ): DVCStateAndOuputs
    {
        var slot := block_share.block.slot;

        if is_slot_for_current_or_future_instances(process, slot) then
            var data := block_share.block;
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
            if process.construct_complete_signed_block(process_with_new_block_share.rcvd_block_shares[slot][data]).isPresent() then                
                    var complete_signed_block := process.construct_complete_signed_block(process_with_new_block_share.rcvd_block_shares[slot][data]).safe_get();                      
                    DVCStateAndOuputs(
                        state := process_with_new_block_share,
                        outputs := getEmptyOuputs().(
                                submitted_data := {complete_signed_block}
                            )
                    )
            else 
                DVCStateAndOuputs(
                    state := process,
                    outputs := getEmptyOuputs()
                )            
        else
            DVCStateAndOuputs(
                state := process,
                outputs := getEmptyOuputs()
            )     
    }

    function f_listen_for_randao_shares(
        process: DVCState,
        randao_share: RandaoShare
    ): DVCStateAndOuputs         
    {
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        then
            var process_with_new_randao_share := 
                    process.(
                        rcvd_randao_shares := process.rcvd_randao_shares[slot := getOrDefault(process.rcvd_randao_shares, slot, {}) + 
                                                                                        {randao_share} ]
                    );     
            f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share
            )
        else
            DVCStateAndOuputs(
                state := process,
                outputs := getEmptyOuputs()
            )
    }

    predicate isMyAttestation(
        a: Attestation,
        bn: BNState<SignedBeaconBlock>,
        block: BeaconBlock,
        valIndex: Optional<ValidatorIndex>
    )
    requires block.body.state_root in bn.state_roots_of_imported_blocks
    {
            && var committee := bn_get_epoch_committees<SignedBeaconBlock>(bn, block.body.state_root, a.data.index);
            && valIndex.Some?
            && valIndex.v in committee
            && var i:nat :| i < |committee| && committee[i] == valIndex.v;
            && i < |a.aggregation_bits|
            && a.aggregation_bits[i]         
    }

    function f_listen_for_new_imported_blocks_helper(
        process: DVCState,
        consensus_instances_on_blocks_already_decided: map<Slot, BeaconBlock>
    ): map<Slot, BeaconBlock>
    {
        if process.latest_proposer_duty.isPresent() then
            var old_instances := 
                    set i | 
                        && i in consensus_instances_on_blocks_already_decided.Keys
                        && i <= process.latest_proposer_duty.safe_get().slot
                    ;
            consensus_instances_on_blocks_already_decided - old_instances
        else
            consensus_instances_on_blocks_already_decided     
    }

    function f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock
    ): DVCStateAndOuputs
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
        var new_consensus_instances_on_blocks_already_decided: map<Slot, BeaconBlock> := 
            map[ block.slot := block ];

        var consensus_instances_on_blocks_already_decided := process.future_consensus_instances_on_blocks_already_decided + new_consensus_instances_on_blocks_already_decided;

        var future_consensus_instances_on_blocks_already_decided := 
            f_listen_for_new_imported_blocks_helper(process, consensus_instances_on_blocks_already_decided);

        var process_after_stopping_consensus_instance :=
                process.(
                    future_consensus_instances_on_blocks_already_decided := future_consensus_instances_on_blocks_already_decided,
                    block_consensus_engine_state := stopBlockConsensusInstances(
                                    process.block_consensus_engine_state,
                                    consensus_instances_on_blocks_already_decided.Keys
                    ),
                    block_shares_to_broadcast := process.block_shares_to_broadcast - consensus_instances_on_blocks_already_decided.Keys,
                    rcvd_block_shares := process.rcvd_block_shares - consensus_instances_on_blocks_already_decided.Keys                    
                );   

        if  && process_after_stopping_consensus_instance.current_proposer_duty.isPresent() 
            && process_after_stopping_consensus_instance.current_proposer_duty.safe_get().slot in consensus_instances_on_blocks_already_decided 
        then
            var decided_beacon_blocks := consensus_instances_on_blocks_already_decided[process.current_proposer_duty.safe_get().slot];
            var new_block_slashing_db := f_update_block_slashing_db(process.block_slashing_db, decided_beacon_blocks);
            var process_after_updating_validity_check := 
                    process_after_stopping_consensus_instance.(
                    current_proposer_duty := None,
                    block_slashing_db := new_block_slashing_db,
                    block_consensus_engine_state := updateBlockConsensusInstanceValidityCheck(
                        process_after_stopping_consensus_instance.block_consensus_engine_state,
                        new_block_slashing_db
                    )                
            );
            f_wrap_DVCState_with_Outputs(process_after_updating_validity_check, getEmptyOuputs())
        else
            f_wrap_DVCState_with_Outputs(process, getEmptyOuputs())
    }

    function f_resend_block_share(
        process: DVCState
    ): DVCStateAndOuputs
    {
        DVCStateAndOuputs(
            state := process,
            outputs := getEmptyOuputs().(
                sent_block_shares :=
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
                sent_randao_shares :=
                    if process.randao_shares_to_broadcast.Keys != {} then
                        multicast_multiple(process.randao_shares_to_broadcast.Values, process.peers)                        
                    else
                        {}
                    )
        )
    }      
}