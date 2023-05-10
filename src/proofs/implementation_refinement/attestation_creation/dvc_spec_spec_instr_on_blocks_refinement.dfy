include "../../../proofs/rs_axioms.dfy"
include "../../../proofs/no_slashable_blocks/common/dvc_block_proposer_instrumented.dfy"
include "../../../specs/dvc/dvc_block_proposer.dfy"
include "../../../common/commons.dfy"


include "../../common/att_helper_pred_fcn.dfy"

module Spec_Spec_NonInstr_Refinement
{
    import opened Types 
    import opened CommonFunctions
        
    import opened BN_Axioms
    import opened RS_Axioms
    import DVC_Block_Proposer_Spec_NonInstr
    import DVC_Block_Proposer_Spec_Instr
    import Block_Consensus_Engine_NonInstr
    import Block_Consensus_Engine_Instr
    import opened Att_Helper_Pred_Fcn


    predicate consensusEngineStateRel(
        cei: Block_Consensus_Engine_Instr.BlockConsensusEngineState,
        ceni: Block_Consensus_Engine_NonInstr.BlockConsensusEngineState
    )
    {
        cei.active_consensus_instances_on_beacon_blocks == ceni.active_consensus_instances_on_beacon_blocks
    }

    predicate DVCStateRel(
        dvci: DVC_Block_Proposer_Spec_Instr.DVCState,
        dvcni: DVC_Block_Proposer_Spec_NonInstr.DVCState
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
        dvcandoi: DVC_Block_Proposer_Spec_Instr.DVCStateAndOuputs,
        dvcandoni: DVC_Block_Proposer_Spec_NonInstr.DVCStateAndOuputs        
    )
    {
        && DVCStateRel(dvcandoi.state, dvcandoni.state)
        && dvcandoi.outputs == dvcandoni.outputs
    }

    lemma refine_init(
        dvci: DVC_Block_Proposer_Spec_Instr.DVCState,
        dvcni: DVC_Block_Proposer_Spec_NonInstr.DVCState,
        dv_pubkey: BLSPubkey,
        peers: set<BLSPubkey>,                    
        construct_complete_signed_randao_reveal: (set<BLSSignature>) -> Optional<BLSSignature>,
        construct_complete_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>,        
        initial_block_slashing_db: set<SlashingDBBlock>,
        rs_pubkey: BLSPubkey
    )
    requires DVC_Block_Proposer_Spec_Instr.Init.requires(
                dvci, 
                dv_pubkey,
                peers,
                construct_complete_signed_randao_reveal,
                construct_complete_signed_block, 
                initial_block_slashing_db,
                rs_pubkey
            )
    requires DVC_Block_Proposer_Spec_Instr.Init(
                dvci, 
                dv_pubkey,
                peers,
                construct_complete_signed_randao_reveal,
                construct_complete_signed_block, 
                initial_block_slashing_db,
                rs_pubkey
            )
    requires DVC_Block_Proposer_Spec_NonInstr.Init.requires(
                dvcni, 
                dv_pubkey,
                peers,
                construct_complete_signed_randao_reveal,
                construct_complete_signed_block, 
                initial_block_slashing_db,
                rs_pubkey
            )
    requires DVC_Block_Proposer_Spec_NonInstr.Init(
                dvcni, 
                dv_pubkey,
                peers,
                construct_complete_signed_randao_reveal,
                construct_complete_signed_block, 
                initial_block_slashing_db,
                rs_pubkey
            )
    ensures && var  dvcoi := 
                    DVC_Block_Proposer_Spec_Instr.DVCStateAndOuputs(
                        dvci,
                        DVC_Block_Proposer_Spec_Instr.getEmptyOuputs()
                    );
            && var  dvconi := 
                    DVC_Block_Proposer_Spec_NonInstr.DVCStateAndOuputs(
                        dvcni,
                        DVC_Block_Proposer_Spec_NonInstr.getEmptyOuputs()
                    );
            && DVCStateAndOuputsRel(dvcoi, dvconi);    
    { }

    lemma refine_f_serve_proposer_duty(
        dvci: DVC_Block_Proposer_Spec_Instr.DVCState,
        dvcni: DVC_Block_Proposer_Spec_NonInstr.DVCState,
        proposer_duty: ProposerDuty
    )
    requires DVC_Block_Proposer_Spec_Instr.f_serve_proposer_duty.requires(dvci, proposer_duty)
    requires DVCStateRel(dvci, dvcni)
    ensures DVC_Block_Proposer_Spec_NonInstr.f_serve_proposer_duty.requires(dvcni, proposer_duty)
    ensures DVCStateAndOuputsRel(
        DVC_Block_Proposer_Spec_Instr.f_serve_proposer_duty(dvci, proposer_duty), 
        DVC_Block_Proposer_Spec_NonInstr.f_serve_proposer_duty(dvcni, proposer_duty)
    );    
    { }

    lemma refine_f_broadcast_randao_share(
        dvci: DVC_Block_Proposer_Spec_Instr.DVCState,
        dvcni: DVC_Block_Proposer_Spec_NonInstr.DVCState,
        proposer_duty: ProposerDuty
    )
    requires DVC_Block_Proposer_Spec_Instr.f_broadcast_randao_share.requires(dvci, proposer_duty)
    requires DVCStateRel(dvci, dvcni)
    ensures DVC_Block_Proposer_Spec_NonInstr.f_broadcast_randao_share.requires(dvcni, proposer_duty)
    ensures DVCStateAndOuputsRel(
        DVC_Block_Proposer_Spec_Instr.f_broadcast_randao_share(dvci, proposer_duty), 
        DVC_Block_Proposer_Spec_NonInstr.f_broadcast_randao_share(dvcni, proposer_duty)
    );    
    { }

    lemma refine_f_check_for_next_duty(
        dvci: DVC_Block_Proposer_Spec_Instr.DVCState,
        dvcni: DVC_Block_Proposer_Spec_NonInstr.DVCState,
        proposer_duty: ProposerDuty
    )
    requires DVC_Block_Proposer_Spec_Instr.f_check_for_next_duty.requires(dvci, proposer_duty)
    requires DVCStateRel(dvci, dvcni)
    ensures DVC_Block_Proposer_Spec_NonInstr.f_check_for_next_duty.requires(dvcni, proposer_duty)
    ensures DVCStateAndOuputsRel(
        DVC_Block_Proposer_Spec_Instr.f_check_for_next_duty(dvci, proposer_duty), 
        DVC_Block_Proposer_Spec_NonInstr.f_check_for_next_duty(dvcni, proposer_duty)
    )    
    {
        var slot := proposer_duty.slot;
        if slot in dvci.future_consensus_instances_on_blocks_already_decided.Keys
        { }
        else
        { }
    }

    lemma refine_f_listen_for_randao_shares(
        dvci: DVC_Block_Proposer_Spec_Instr.DVCState,
        dvcni: DVC_Block_Proposer_Spec_NonInstr.DVCState,
        randao_share: RandaoShare
    )
    requires DVC_Block_Proposer_Spec_Instr.f_listen_for_randao_shares.requires(dvci, randao_share)
    requires DVCStateRel(dvci, dvcni)
    ensures DVC_Block_Proposer_Spec_NonInstr.f_listen_for_randao_shares.requires(dvcni, randao_share)
    ensures DVCStateAndOuputsRel(
        DVC_Block_Proposer_Spec_Instr.f_listen_for_randao_shares(dvci, randao_share), 
        DVC_Block_Proposer_Spec_NonInstr.f_listen_for_randao_shares(dvcni, randao_share)
    );    
    { }

    lemma refine_f_start_consensus_if_can_construct_randao_share(
        dvci: DVC_Block_Proposer_Spec_Instr.DVCState,
        dvcni: DVC_Block_Proposer_Spec_NonInstr.DVCState
    )
    requires DVC_Block_Proposer_Spec_Instr.f_start_consensus_if_can_construct_randao_share.requires(dvci)
    requires DVCStateRel(dvci, dvcni)
    ensures DVC_Block_Proposer_Spec_NonInstr.f_start_consensus_if_can_construct_randao_share.requires(dvcni)
    ensures DVCStateAndOuputsRel(
        DVC_Block_Proposer_Spec_Instr.f_start_consensus_if_can_construct_randao_share(dvci), 
        DVC_Block_Proposer_Spec_NonInstr.f_start_consensus_if_can_construct_randao_share(dvcni)
    );    
    { }

    lemma refine_f_block_consensus_decided(
        dvci: DVC_Block_Proposer_Spec_Instr.DVCState,
        dvcni: DVC_Block_Proposer_Spec_NonInstr.DVCState,
        id: Slot,
        block: BeaconBlock
    )
    requires DVC_Block_Proposer_Spec_Instr.f_block_consensus_decided.requires(dvci, id, block)
    requires DVCStateRel(dvci, dvcni)
    ensures DVC_Block_Proposer_Spec_NonInstr.f_block_consensus_decided.requires(dvcni, id, block)
    ensures DVCStateAndOuputsRel(
        DVC_Block_Proposer_Spec_Instr.f_block_consensus_decided(dvci, id, block), 
        DVC_Block_Proposer_Spec_NonInstr.f_block_consensus_decided(dvcni, id, block)
    );       
    { }

    lemma refine_f_listen_for_block_signature_shares(
        dvci: DVC_Block_Proposer_Spec_Instr.DVCState,
        dvcni: DVC_Block_Proposer_Spec_NonInstr.DVCState,
        block_share: SignedBeaconBlock
    )
    requires DVC_Block_Proposer_Spec_Instr.f_listen_for_block_signature_shares.requires(dvci, block_share)
    requires DVCStateRel(dvci, dvcni)
    ensures DVC_Block_Proposer_Spec_NonInstr.f_listen_for_block_signature_shares.requires(dvcni, block_share)
    ensures DVCStateAndOuputsRel(
        DVC_Block_Proposer_Spec_Instr.f_listen_for_block_signature_shares(dvci, block_share), 
        DVC_Block_Proposer_Spec_NonInstr.f_listen_for_block_signature_shares(dvcni, block_share)
    );    
    { }     

    

    lemma refine_f_listen_for_new_imported_blocks(
        dvci: DVC_Block_Proposer_Spec_Instr.DVCState,
        dvcni: DVC_Block_Proposer_Spec_NonInstr.DVCState,
        block: BeaconBlock
    )
    requires DVC_Block_Proposer_Spec_Instr.f_listen_for_new_imported_blocks.requires(dvci, block)
    requires DVCStateRel(dvci, dvcni)
    ensures DVC_Block_Proposer_Spec_NonInstr.f_listen_for_new_imported_blocks.requires(dvcni, block)
    ensures DVCStateAndOuputsRel(
        DVC_Block_Proposer_Spec_Instr.f_listen_for_new_imported_blocks(dvci, block), 
        DVC_Block_Proposer_Spec_NonInstr.f_listen_for_new_imported_blocks(dvcni, block)
    );     
    { }

    lemma refine_f_resend_randao_share(
        dvci: DVC_Block_Proposer_Spec_Instr.DVCState,
        dvcni: DVC_Block_Proposer_Spec_NonInstr.DVCState
    )
    requires DVC_Block_Proposer_Spec_Instr.f_resend_randao_share.requires(dvci)
    requires DVCStateRel(dvci, dvcni)
    ensures DVC_Block_Proposer_Spec_NonInstr.f_resend_randao_share.requires(dvcni)
    ensures DVCStateAndOuputsRel(
        DVC_Block_Proposer_Spec_Instr.f_resend_randao_share(dvci), 
        DVC_Block_Proposer_Spec_NonInstr.f_resend_randao_share(dvcni)
    ); 
    { }

    lemma refine_f_resend_block_share(
        dvci: DVC_Block_Proposer_Spec_Instr.DVCState,
        dvcni: DVC_Block_Proposer_Spec_NonInstr.DVCState
    )
    requires DVC_Block_Proposer_Spec_Instr.f_resend_block_share.requires(dvci)
    requires DVCStateRel(dvci, dvcni)
    ensures DVC_Block_Proposer_Spec_NonInstr.f_resend_block_share.requires(dvcni)
    ensures DVCStateAndOuputsRel(
        DVC_Block_Proposer_Spec_Instr.f_resend_block_share(dvci), 
        DVC_Block_Proposer_Spec_NonInstr.f_resend_block_share(dvcni)
    ); 
    { }

    lemma refine_f_process_event(
        dvci: DVC_Block_Proposer_Spec_Instr.DVCState,
        dvcni: DVC_Block_Proposer_Spec_NonInstr.DVCState,
        event: BlockEvent
    )
    requires DVC_Block_Proposer_Spec_Instr.f_process_event.requires(dvci, event)
    requires DVCStateRel(dvci, dvcni)
    ensures DVC_Block_Proposer_Spec_NonInstr.f_process_event.requires(dvcni, event)
    ensures DVCStateAndOuputsRel(
        DVC_Block_Proposer_Spec_Instr.f_process_event(dvci, event), 
        DVC_Block_Proposer_Spec_NonInstr.f_process_event(dvcni, event)
    ); 
    {
        match event 
            case ServeProposerDuty(proposer_duty) => 
                refine_f_serve_proposer_duty(dvci, dvcni, proposer_duty);
            case BlockConsensusDecided(id, block) => 
                refine_f_block_consensus_decided(dvci, dvcni, id,  block);
            case ReceiveRandaoShare(randao_share) => 
                refine_f_listen_for_randao_shares(dvci, dvcni, randao_share);
            case ReceiveSignedBeaconBlock(block_share) => 
                refine_f_listen_for_block_signature_shares(dvci, dvcni, block_share);
            case ImportedNewBlock(block) => 
                refine_f_listen_for_new_imported_blocks(dvci, dvcni, block);
            case ResendRandaoRevealSignatureShare => 
                refine_f_resend_randao_share(dvci, dvcni);
            case ResendBlockShare => 
                refine_f_resend_block_share(dvci, dvcni);
            case NoEvent => 
    }    
}
