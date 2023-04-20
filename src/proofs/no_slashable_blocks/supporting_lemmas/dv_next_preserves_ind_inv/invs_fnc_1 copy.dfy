include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_block_proposer.dfy"
include "../inv.dfy"
include "../../../common/helper_sets_lemmas.dfy"
include "../../common/common_proofs.dfy"
include "../../common/block_dvc_spec_axioms.dfy"

include "../../../../common/block_proposer/block_types.dfy"
include "../../../../common/block_proposer/block_common_functions.dfy"
include "../../../../common/block_proposer/block_signing_functions.dfy"
include "../../common/dvc_block_proposer_instrumented.dfy"
include "../../../../specs/consensus/block_consensus.dfy"
include "../../../../specs/network/block_network.dfy"
include "../inv.dfy"
include "../../../common/helper_sets_lemmas.dfy"

include "../../../common/helper_pred_fcn.dfy"

include "invs_fnc_1.dfy"


module Fnc_Invs_Copy
{
    import opened Block_Types 
    import opened Block_Signing_Functions
    import opened Block_Common_Functions
    import opened Block_Consensus_Spec
    import opened Block_Network_Spec
    import opened DVC_Block_Proposer_Spec_Instr
    import opened Block_Inv_With_Empty_Initial_Block_Slashing_DB
    import opened Helper_Sets_Lemmas
    import opened Common_Proofs_For_Block_Proposer
    import opened DVC_Block_Proposer_Spec_Axioms
    import opened Helper_Pred_Fcn
    import opened DV_Block_Proposer_Spec
    import opened Fnc_Invs_1

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process')
    { }

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process')
    { }

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process')
    { }      

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process')
    { 
        var slot := randao_share.slot;
        var active_consensus_instances_on_beacon_blocks := process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := getOrDefault(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process')
    { }

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process')
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
        var process_after_adding_randao_share :=
            process.(
                randao_shares_to_broadcast := process.randao_shares_to_broadcast[proposer_duty.slot := randao_share]
            );

        lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        
        lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );
    } 

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process')
    { }  

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process')
    { }

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process')
    { }  

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process')
    { }  

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process')
    { }  

    // lemma lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_dv_next(
    //     dv: DVState,
    //     event: DV_Block_Proposer_Spec.Event,
    //     dv': DVState
    // )    
    // requires NextEventPreCond(dv, event)
    // requires NextEvent(dv, event, dv')  
    // requires inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block(dv)
    // ensures inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block(dv')
    // {        
    //     match event 
    //     {
    //         case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
    //             var process := dv.honest_nodes_states[node];
    //             var process' := dv'.honest_nodes_states[node];
    //             match nodeEvent
    //             {
    //                 case ServeProposerDuty(proposer_duty) =>     
    //                     lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_serve_proposer_duty(process, proposer_duty, process');
                    
    //                 case ReceiveRandaoShare(randao_share) =>
    //                     lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_listen_for_randao_shares(process, randao_share, process');    
                        
    //                 case BlockConsensusDecided(id, decided_beacon_block) => 
    //                     if f_block_consensus_decided.requires(process, id, decided_beacon_block)
    //                     {
    //                         lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_block_consensus_decided(process, id, decided_beacon_block, process');      
    //                     }                 
                        
    //                 case ReceiveSignedBeaconBlock(block_share) =>                         
    //                     lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_listen_for_block_signature_shares(process, block_share, process');                        
   
    //                 case ImportedNewBlock(block) => 
    //                     var process := f_add_block_to_bn(process, nodeEvent.block);
    //                     lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_listen_for_new_imported_blocks(process, block, process');                        
                                                
    //                 case ResendRandaoRevealSignatureShare =>

    //                 case ResendBlockShare =>
                        
    //                 case NoEvent => 
                        
    //             }

    //         case AdversaryTakingStep(node, new_randao_shares_sent, new_sent_block_shares, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) =>
                
    //     }   
    // } 

    

     
}