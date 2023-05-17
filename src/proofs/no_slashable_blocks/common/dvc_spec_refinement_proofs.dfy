include "../../../proofs/rs_axioms.dfy"
include "../../../proofs/no_slashable_blocks/common/dvc_block_proposer_instrumented.dfy"
include "../../../specs/dvc/dvc_block_proposer.dfy"
include "../../../common/commons.dfy"

module Spec_Spec_Non_Instr_Refinement
{
    import opened Types 
    import opened Common_Functions
        
    import opened BN_Axioms
    import opened RS_Axioms
    import Non_Instr_Block_DVC
    import Block_DVC
    import Non_Instr_Consensus_Engine
    import Consensus_Engine


    predicate consensusEngineStateRel(
        cei: ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>,
        ceni: NonInstrConsensusEngineState<BlockConsensusValidityCheckState>
    )
    {
        cei.active_consensus_instances == ceni.active_consensus_instances
    }

    predicate DVCStateRel(
        dvci: BlockDVCState,
        dvcni: NonInstrBlockDVCState
    )
    {
        && dvci.current_proposer_duty == dvcni.current_proposer_duty
        && dvci.latest_proposer_duty == dvcni.latest_proposer_duty
        && dvci.block_slashing_db == dvcni.block_slashing_db
        && dvci.rcvd_randao_shares == dvcni.rcvd_randao_shares
        && dvci.rcvd_block_shares == dvcni.rcvd_block_shares
        && dvci.construct_complete_signed_randao_reveal == dvcni.construct_complete_signed_randao_reveal
        && dvci.construct_complete_signed_block == dvcni.construct_complete_signed_block
        && dvci.randao_shares_to_broadcast == dvcni.randao_shares_to_broadcast
        && dvci.block_shares_to_broadcast == dvcni.block_shares_to_broadcast
        && dvci.peers == dvcni.peers
        && dvci.dv_pubkey == dvcni.dv_pubkey
        && dvci.future_consensus_instances_on_blocks_already_decided == dvcni.future_consensus_instances_on_blocks_already_decided
        && dvci.bn == dvcni.bn
        && dvci.rs == dvcni.rs
        && consensusEngineStateRel(dvci.block_consensus_engine_state, dvcni.block_consensus_engine_state)
    }

    predicate DVCStateAndOuputsRel(
        dvcandoi: DVCStateAndOuputs<BlockDVCState, BlockOutputs>,
        dvcandoni: DVCStateAndOuputs<NonInstrBlockDVCState, BlockOutputs>        
    )
    {
        && DVCStateRel(dvcandoi.state, dvcandoni.state)
        && dvcandoi.outputs == dvcandoni.outputs
    }

    lemma lem_refine_init(
        dvci: BlockDVCState,
        dvcni: NonInstrBlockDVCState,
        dv_pubkey: BLSPubkey,
        peers: set<BLSPubkey>,                    
        construct_complete_signed_randao_reveal: (set<BLSSignature>) -> Optional<BLSSignature>,
        construct_complete_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>,        
        initial_block_slashing_db: set<SlashingDBBlock>,
        rs_pubkey: BLSPubkey
    )
    requires Block_DVC.init.requires(
                dvci, 
                dv_pubkey,
                peers,
                construct_complete_signed_randao_reveal,
                construct_complete_signed_block, 
                initial_block_slashing_db,
                rs_pubkey
            )
    requires Block_DVC.init(
                dvci, 
                dv_pubkey,
                peers,
                construct_complete_signed_randao_reveal,
                construct_complete_signed_block, 
                initial_block_slashing_db,
                rs_pubkey
            )
    requires Non_Instr_Block_DVC.init.requires(
                dvcni, 
                dv_pubkey,
                peers,
                construct_complete_signed_randao_reveal,
                construct_complete_signed_block, 
                initial_block_slashing_db,
                rs_pubkey
            )
    requires Non_Instr_Block_DVC.init(
                dvcni, 
                dv_pubkey,
                peers,
                construct_complete_signed_randao_reveal,
                construct_complete_signed_block, 
                initial_block_slashing_db,
                rs_pubkey
            )
    ensures && var  dvcoi := 
                    DVCStateAndOuputs(
                        dvci,
                        f_get_empty_block_ouputs()
                    );
            && var  dvconi := 
                    DVCStateAndOuputs(
                        dvcni,
                        f_get_empty_block_ouputs()
                    );
            && DVCStateAndOuputsRel(dvcoi, dvconi);    
    { }

    lemma lem_refine_f_serve_proposer_duty(
        dvci: BlockDVCState,
        dvcni: NonInstrBlockDVCState,
        proposer_duty: ProposerDuty
    )
    requires Block_DVC.f_serve_proposer_duty.requires(dvci, proposer_duty)
    requires DVCStateRel(dvci, dvcni)
    ensures Non_Instr_Block_DVC.f_serve_proposer_duty.requires(dvcni, proposer_duty)
    ensures DVCStateAndOuputsRel(
        Block_DVC.f_serve_proposer_duty(dvci, proposer_duty), 
        Non_Instr_Block_DVC.f_serve_proposer_duty(dvcni, proposer_duty)
    );    
    { }

    lemma lem_refine_f_broadcast_randao_share(
        dvci: BlockDVCState,
        dvcni: NonInstrBlockDVCState,
        proposer_duty: ProposerDuty
    )
    requires Block_DVC.f_broadcast_randao_share.requires(dvci, proposer_duty)
    requires DVCStateRel(dvci, dvcni)
    ensures Non_Instr_Block_DVC.f_broadcast_randao_share.requires(dvcni, proposer_duty)
    ensures DVCStateAndOuputsRel(
        Block_DVC.f_broadcast_randao_share(dvci, proposer_duty), 
        Non_Instr_Block_DVC.f_broadcast_randao_share(dvcni, proposer_duty)
    );    
    { }

    lemma lem_refine_f_check_for_next_duty(
        dvci: BlockDVCState,
        dvcni: NonInstrBlockDVCState,
        proposer_duty: ProposerDuty
    )
    requires Block_DVC.f_check_for_next_duty.requires(dvci, proposer_duty)
    requires DVCStateRel(dvci, dvcni)
    ensures Non_Instr_Block_DVC.f_check_for_next_duty.requires(dvcni, proposer_duty)
    ensures DVCStateAndOuputsRel(
        Block_DVC.f_check_for_next_duty(dvci, proposer_duty), 
        Non_Instr_Block_DVC.f_check_for_next_duty(dvcni, proposer_duty)
    )    
    {
        var slot := proposer_duty.slot;
        if slot in dvci.future_consensus_instances_on_blocks_already_decided.Keys
        { }
        else
        { }
    }

    lemma lem_refine_f_listen_for_randao_shares(
        dvci: BlockDVCState,
        dvcni: NonInstrBlockDVCState,
        randao_share: RandaoShare
    )
    requires Block_DVC.f_listen_for_randao_shares.requires(dvci, randao_share)
    requires DVCStateRel(dvci, dvcni)
    ensures Non_Instr_Block_DVC.f_listen_for_randao_shares.requires(dvcni, randao_share)
    ensures DVCStateAndOuputsRel(
        Block_DVC.f_listen_for_randao_shares(dvci, randao_share), 
        Non_Instr_Block_DVC.f_listen_for_randao_shares(dvcni, randao_share)
    );    
    { }

    lemma lem_refine_f_start_consensus_if_can_construct_randao_share(
        dvci: BlockDVCState,
        dvcni: NonInstrBlockDVCState
    )
    requires Block_DVC.f_start_consensus_if_can_construct_randao_share.requires(dvci)
    requires DVCStateRel(dvci, dvcni)
    ensures Non_Instr_Block_DVC.f_start_consensus_if_can_construct_randao_share.requires(dvcni)
    ensures DVCStateAndOuputsRel(
        Block_DVC.f_start_consensus_if_can_construct_randao_share(dvci), 
        Non_Instr_Block_DVC.f_start_consensus_if_can_construct_randao_share(dvcni)
    );    
    { }

    lemma lem_refine_f_block_consensus_decided(
        dvci: BlockDVCState,
        dvcni: NonInstrBlockDVCState,
        id: Slot,
        block: BeaconBlock
    )
    requires Block_DVC.f_block_consensus_decided.requires(dvci, id, block)
    requires DVCStateRel(dvci, dvcni)
    ensures Non_Instr_Block_DVC.f_block_consensus_decided.requires(dvcni, id, block)
    ensures DVCStateAndOuputsRel(
        Block_DVC.f_block_consensus_decided(dvci, id, block), 
        Non_Instr_Block_DVC.f_block_consensus_decided(dvcni, id, block)
    );       
    { }

    lemma lem_refine_f_listen_for_block_signature_shares(
        dvci: BlockDVCState,
        dvcni: NonInstrBlockDVCState,
        block_share: SignedBeaconBlock
    )
    requires Block_DVC.f_listen_for_block_signature_shares.requires(dvci, block_share)
    requires DVCStateRel(dvci, dvcni)
    ensures Non_Instr_Block_DVC.f_listen_for_block_signature_shares.requires(dvcni, block_share)
    ensures DVCStateAndOuputsRel(
        Block_DVC.f_listen_for_block_signature_shares(dvci, block_share), 
        Non_Instr_Block_DVC.f_listen_for_block_signature_shares(dvcni, block_share)
    );    
    { }     

    

    lemma lem_refine_f_listen_for_new_imported_blocks(
        dvci: BlockDVCState,
        dvcni: NonInstrBlockDVCState,
        block: BeaconBlock
    )
    requires Block_DVC.f_listen_for_new_imported_blocks.requires(dvci, block)
    requires DVCStateRel(dvci, dvcni)
    ensures Non_Instr_Block_DVC.f_listen_for_new_imported_blocks.requires(dvcni, block)
    ensures DVCStateAndOuputsRel(
        Block_DVC.f_listen_for_new_imported_blocks(dvci, block), 
        Non_Instr_Block_DVC.f_listen_for_new_imported_blocks(dvcni, block)
    );     
    { }

    lemma lem_refine_f_resend_randao_shares(
        dvci: BlockDVCState,
        dvcni: NonInstrBlockDVCState
    )
    requires Block_DVC.f_resend_randao_shares.requires(dvci)
    requires DVCStateRel(dvci, dvcni)
    ensures Non_Instr_Block_DVC.f_resend_randao_shares.requires(dvcni)
    ensures DVCStateAndOuputsRel(
        Block_DVC.f_resend_randao_shares(dvci), 
        Non_Instr_Block_DVC.f_resend_randao_shares(dvcni)
    ); 
    { }

    lemma lem_refine_f_resend_block_shares(
        dvci: BlockDVCState,
        dvcni: NonInstrBlockDVCState
    )
    requires Block_DVC.f_resend_block_shares.requires(dvci)
    requires DVCStateRel(dvci, dvcni)
    ensures Non_Instr_Block_DVC.f_resend_block_shares.requires(dvcni)
    ensures DVCStateAndOuputsRel(
        Block_DVC.f_resend_block_shares(dvci), 
        Non_Instr_Block_DVC.f_resend_block_shares(dvcni)
    ); 
    { }

    lemma lem_refine_f_process_event(
        dvci: BlockDVCState,
        dvcni: NonInstrBlockDVCState,
        event: BlockEvent
    )
    requires Block_DVC.f_process_event.requires(dvci, event)
    requires DVCStateRel(dvci, dvcni)
    ensures Non_Instr_Block_DVC.f_process_event.requires(dvcni, event)
    ensures DVCStateAndOuputsRel(
        Block_DVC.f_process_event(dvci, event), 
        Non_Instr_Block_DVC.f_process_event(dvcni, event)
    ); 
    {
        match event 
            case ServeProposerDuty(proposer_duty) => 
                lem_refine_f_serve_proposer_duty(dvci, dvcni, proposer_duty);
            case BlockConsensusDecided(id, block) => 
                lem_refine_f_block_consensus_decided(dvci, dvcni, id,  block);
            case ReceiveRandaoShare(randao_share) => 
                lem_refine_f_listen_for_randao_shares(dvci, dvcni, randao_share);
            case ReceiveSignedBeaconBlock(block_share) => 
                lem_refine_f_listen_for_block_signature_shares(dvci, dvcni, block_share);
            case ImportedNewBlock(block) => 
                lem_refine_f_listen_for_new_imported_blocks(dvci, dvcni, block);
            case ResendRandaoRevealSignatureShare => 
                lem_refine_f_resend_randao_shares(dvci, dvcni);
            case ResendBlockShare => 
                lem_refine_f_resend_block_shares(dvci, dvcni);
            case NoEvent => 
    }    
}
