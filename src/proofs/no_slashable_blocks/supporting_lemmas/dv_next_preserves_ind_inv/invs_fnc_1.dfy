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


module Fnc_Invs_1
{
    import opened Block_Types 
    import opened Block_Signing_Functions
    import opened Block_Common_Functions
    import opened Block_Consensus_Spec
    import opened Block_Network_Spec
    import opened DV_Block_Proposer_Spec
    import opened DVC_Block_Proposer_Spec_Instr
    import opened Block_Inv_With_Empty_Initial_Block_Slashing_DB
    import opened Helper_Sets_Lemmas
    import opened Common_Proofs_For_Block_Proposer
    import opened DVC_Block_Proposer_Spec_Axioms
    import opened Helper_Pred_Fcn

    lemma lem_updated_all_rcvd_duties_f_terminate_current_proposer_duty(
        dvc: DVCState,
        dvc': DVCState
    )  
    requires f_terminate_current_proposer_duty.requires(dvc)
    requires dvc' == f_terminate_current_proposer_duty(dvc)
    ensures dvc'.all_rcvd_duties == dvc.all_rcvd_duties 
    { }

    lemma lem_updated_all_rcvd_duties_f_check_for_next_duty(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_check_for_next_duty.requires(dvc, proposer_duty)
    requires dvc' == f_check_for_next_duty(dvc, proposer_duty).state
    ensures dvc'.all_rcvd_duties == dvc.all_rcvd_duties
    { }

    lemma lem_updated_all_rcvd_duties_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    ensures dvc'.all_rcvd_duties == dvc.all_rcvd_duties
    { }
    
    lemma lem_updated_all_rcvd_duties_f_serve_proposer_duty(
        dvc: DVCState,
        proposer_duty: ProposerDuty,
        dvc': DVCState
    )  
    requires f_serve_proposer_duty.requires(dvc, proposer_duty)
    requires dvc' == f_serve_proposer_duty(dvc, proposer_duty).state
    ensures dvc'.all_rcvd_duties == dvc.all_rcvd_duties + {proposer_duty}    
    {         
        var process_after_stopping_current_duty := 
            f_terminate_current_proposer_duty(dvc);

        lem_updated_all_rcvd_duties_f_terminate_current_proposer_duty(
            dvc,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);                

        lem_updated_all_rcvd_duties_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty, 
            dvc'
        );
    }

    lemma lem_updated_all_rcvd_duties_f_listen_for_randao_shares(
        process: DVCState,
        randao_share: RandaoShare,
        process': DVCState
    )
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state
    ensures process.all_rcvd_duties == process'.all_rcvd_duties
    { }

    lemma lem_updated_all_rcvd_duties_f_start_consensus_if_can_construct_randao_share(
        dvc: DVCState, 
        dvc': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(dvc)
    requires dvc' == f_start_consensus_if_can_construct_randao_share(dvc).state
    ensures dvc'.all_rcvd_duties == dvc.all_rcvd_duties        
    { }  

    lemma lem_updated_all_rcvd_duties_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    ensures process'.all_rcvd_duties == process.all_rcvd_duties
    { }  

    lemma lem_updated_all_rcvd_duties_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    ensures process.all_rcvd_duties == process'.all_rcvd_duties
    { }

    lemma lem_updated_all_rcvd_duties_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    ensures process.all_rcvd_duties == process'.all_rcvd_duties
    { }   

    lemma lem_updated_all_rcvd_duties_f_resend_randao_share(
        s: DVCState,
        s': DVCState 
    )
    requires f_resend_randao_share.requires(s)
    requires s' == f_resend_randao_share(s).state
    requires s.all_rcvd_duties == s'.all_rcvd_duties
    { } 

    lemma lem_updated_all_rcvd_duties_f_resend_block_share(
        s: DVCState,
        s': DVCState 
    )
    requires f_resend_block_share.requires(s)
    requires s' == f_resend_block_share(s).state
    requires s.all_rcvd_duties == s'.all_rcvd_duties
    { } 

    lemma lem_inv_current_proposer_duty_is_a_rcvd_duty_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(process)
    ensures inv_current_proposer_duty_is_a_rcvd_duty_body(process')
    { }

    lemma lem_inv_current_proposer_duty_is_a_rcvd_duty_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(process)
    ensures inv_current_proposer_duty_is_a_rcvd_duty_body(process')
    { }      

    lemma lem_inv_current_proposer_duty_is_a_rcvd_duty_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state    
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(process)
    ensures inv_current_proposer_duty_is_a_rcvd_duty_body(process')
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
            lem_inv_current_proposer_duty_is_a_rcvd_duty_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_current_proposer_duty_is_a_rcvd_duty_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires proposer_duty in process.all_rcvd_duties
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(process)
    ensures inv_current_proposer_duty_is_a_rcvd_duty_body(process')
    { }

    lemma lem_inv_current_proposer_duty_is_a_rcvd_duty_body_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires proposer_duty in dvc.all_rcvd_duties
    requires dvc.latest_proposer_duty.isPresent()
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(dvc)
    ensures inv_current_proposer_duty_is_a_rcvd_duty_body(dvc')
    { 
        var slot := proposer_duty.slot;
        var fork_version := bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, dvc.rs);
        var randao_share := 
            RandaoShare(
                proposer_duty := proposer_duty,
                slot := slot,
                signing_root := randao_reveal_signing_root,
                signature := randao_reveal_signature_share
            );
        var process_after_adding_randao_share :=
            dvc.(
                randao_shares_to_broadcast := dvc.randao_shares_to_broadcast[proposer_duty.slot := randao_share]
            );

        lem_inv_current_proposer_duty_is_a_rcvd_duty_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc'
        );
    }

    lemma lem_inv_current_proposer_duty_is_a_rcvd_duty_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state

    requires inv_current_proposer_duty_is_a_rcvd_duty_body(process)
    ensures inv_current_proposer_duty_is_a_rcvd_duty_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        
        lem_inv_current_proposer_duty_is_a_rcvd_duty_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
        
        lem_inv_current_proposer_duty_is_a_rcvd_duty_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_current_proposer_duty_is_a_rcvd_duty_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(process)
    ensures inv_current_proposer_duty_is_a_rcvd_duty_body(process')
    { }  

    lemma lem_inv_current_proposer_duty_is_a_rcvd_duty_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(process)
    ensures inv_current_proposer_duty_is_a_rcvd_duty_body(process')
    { }

    lemma lem_inv_current_proposer_duty_is_a_rcvd_duty_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(process)
    ensures inv_current_proposer_duty_is_a_rcvd_duty_body(process')
    { }  

    lemma lem_inv_current_proposer_duty_is_a_rcvd_duty_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(process)
    ensures inv_current_proposer_duty_is_a_rcvd_duty_body(process')
    { }  

    lemma lem_inv_current_proposer_duty_is_a_rcvd_duty_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(process)
    ensures inv_current_proposer_duty_is_a_rcvd_duty_body(process')
    { }  

    lemma lem_inv_latest_served_duty_is_a_rcvd_duty_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_latest_served_duty_is_a_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_a_rcvd_duty_body(process')
    { }

    lemma lem_inv_latest_served_duty_is_a_rcvd_duty_body_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_latest_served_duty_is_a_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_a_rcvd_duty_body(process')
    { } 

    lemma lem_inv_latest_served_duty_is_a_rcvd_duty_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state    
    requires inv_latest_served_duty_is_a_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_a_rcvd_duty_body(process')
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
            lem_inv_latest_served_duty_is_a_rcvd_duty_body_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }  

    lemma lem_inv_latest_served_duty_is_a_rcvd_duty_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires proposer_duty in process.all_rcvd_duties
    requires inv_latest_served_duty_is_a_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_a_rcvd_duty_body(process')
    { }

    lemma lem_inv_latest_served_duty_is_a_rcvd_duty_body_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires proposer_duty in dvc.all_rcvd_duties
    requires dvc.latest_proposer_duty.isPresent()
    requires inv_latest_served_duty_is_a_rcvd_duty_body(dvc)
    ensures inv_latest_served_duty_is_a_rcvd_duty_body(dvc')
    { 
        var slot := proposer_duty.slot;
        var fork_version := bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, dvc.rs);
        var randao_share := 
            RandaoShare(
                proposer_duty := proposer_duty,
                slot := slot,
                signing_root := randao_reveal_signing_root,
                signature := randao_reveal_signature_share
            );
        var process_after_adding_randao_share :=
            dvc.(
                randao_shares_to_broadcast := dvc.randao_shares_to_broadcast[proposer_duty.slot := randao_share]
            );

        lem_inv_latest_served_duty_is_a_rcvd_duty_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc'
        );
    }

    lemma lem_inv_latest_served_duty_is_a_rcvd_duty_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_latest_served_duty_is_a_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_a_rcvd_duty_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);

        lem_inv_latest_served_duty_is_a_rcvd_duty_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_latest_served_duty_is_a_rcvd_duty_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_latest_served_duty_is_a_rcvd_duty_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_latest_served_duty_is_a_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_a_rcvd_duty_body(process')
    { }  

    lemma lem_inv_latest_served_duty_is_a_rcvd_duty_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_latest_served_duty_is_a_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_a_rcvd_duty_body(process')
    { }

    lemma lem_inv_latest_served_duty_is_a_rcvd_duty_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_latest_served_duty_is_a_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_a_rcvd_duty_body(process')
    { }  

    lemma lem_inv_latest_served_duty_is_a_rcvd_duty_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_latest_served_duty_is_a_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_a_rcvd_duty_body(process')
    { }  

    lemma lem_inv_latest_served_duty_is_a_rcvd_duty_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_latest_served_duty_is_a_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_a_rcvd_duty_body(process')
    { }  

    lemma lem_inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(process)
    ensures inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(process')
    { }

    lemma lem_inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(process)
    ensures inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(process')
    { }      

    lemma lem_inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state    
    requires inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(process)
    ensures inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(process')
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
            lem_inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }   

    lemma lem_inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires proposer_duty in process.all_rcvd_duties
    requires inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(process)
    ensures inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(process')
    { }

    lemma lem_inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires proposer_duty in dvc.all_rcvd_duties
    requires dvc.latest_proposer_duty.isPresent()
    requires inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(dvc)
    ensures inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(dvc')
    { 
        var slot := proposer_duty.slot;
        var fork_version := bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, dvc.rs);
        var randao_share := 
            RandaoShare(
                proposer_duty := proposer_duty,
                slot := slot,
                signing_root := randao_reveal_signing_root,
                signature := randao_reveal_signature_share
            );
        var process_after_adding_randao_share :=
            dvc.(
                randao_shares_to_broadcast := dvc.randao_shares_to_broadcast[proposer_duty.slot := randao_share]
            );

        lem_inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc'
        );
    }

    lemma lem_inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(process)
    ensures inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);

        lem_inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );  
    } 

    lemma lem_inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(process)
    ensures inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(process')
    { }

    lemma lem_inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(process)
    ensures inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(process')
    { }

    lemma lem_inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(process)
    ensures inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(process')
    { }  

    lemma lem_inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(process)
    ensures inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(process')
    { }  

    lemma lem_inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(process)
    ensures inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(process')
    { }  

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process)
    ensures inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process)
    ensures inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state    
    requires inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process)
    ensures inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process')
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
            lem_inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }  

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires proposer_duty in process.all_rcvd_duties
    requires inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process)
    ensures inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires proposer_duty in dvc.all_rcvd_duties
    requires dvc.latest_proposer_duty.isPresent()
    requires inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(dvc)
    ensures inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(dvc')
    { 
        var slot := proposer_duty.slot;
        var fork_version := bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, dvc.rs);
        var randao_share := 
            RandaoShare(
                proposer_duty := proposer_duty,
                slot := slot,
                signing_root := randao_reveal_signing_root,
                signature := randao_reveal_signature_share
            );
        var process_after_adding_randao_share :=
            dvc.(
                randao_shares_to_broadcast := dvc.randao_shares_to_broadcast[proposer_duty.slot := randao_share]
            );

        lem_inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc'
        );
    }

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process)
    ensures inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);

        lem_inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    }

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process)
    ensures inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process)
    ensures inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process)
    ensures inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process)
    ensures inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process)
    ensures inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process')
    { }  
    
    lemma lem_inv_available_current_proposer_duty_is_latest_proposer_duty_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_available_current_proposer_duty_is_latest_proposer_duty_body(process')
    { }    

    lemma lem_inv_available_current_proposer_duty_is_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_available_current_proposer_duty_is_latest_proposer_duty_body(process')
    { }    

    lemma lem_inv_available_current_proposer_duty_is_latest_proposer_duty_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state    
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_available_current_proposer_duty_is_latest_proposer_duty_body(process')
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
            lem_inv_available_current_proposer_duty_is_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    } 

    lemma lem_inv_available_current_proposer_duty_is_latest_proposer_duty_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires proposer_duty in process.all_rcvd_duties
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_available_current_proposer_duty_is_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_available_current_proposer_duty_is_latest_proposer_duty_body_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires proposer_duty in dvc.all_rcvd_duties
    requires dvc.latest_proposer_duty.isPresent()
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(dvc)
    ensures inv_available_current_proposer_duty_is_latest_proposer_duty_body(dvc')
    { 
        var slot := proposer_duty.slot;
        var fork_version := bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, dvc.rs);
        var randao_share := 
            RandaoShare(
                proposer_duty := proposer_duty,
                slot := slot,
                signing_root := randao_reveal_signing_root,
                signature := randao_reveal_signature_share
            );
        var process_after_adding_randao_share :=
            dvc.(
                randao_shares_to_broadcast := dvc.randao_shares_to_broadcast[proposer_duty.slot := randao_share]
            );
        assert inv_available_current_proposer_duty_is_latest_proposer_duty_body(process_after_adding_randao_share);
        lem_inv_available_current_proposer_duty_is_latest_proposer_duty_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc'
        );
    }

    lemma lem_inv_available_current_proposer_duty_is_latest_proposer_duty_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_available_current_proposer_duty_is_latest_proposer_duty_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);

        lem_inv_available_current_proposer_duty_is_latest_proposer_duty_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_available_current_proposer_duty_is_latest_proposer_duty_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_available_current_proposer_duty_is_latest_proposer_duty_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_available_current_proposer_duty_is_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_available_current_proposer_duty_is_latest_proposer_duty_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_available_current_proposer_duty_is_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_available_current_proposer_duty_is_latest_proposer_duty_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_available_current_proposer_duty_is_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_available_current_proposer_duty_is_latest_proposer_duty_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_available_current_proposer_duty_is_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_available_current_proposer_duty_is_latest_proposer_duty_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_available_current_proposer_duty_is_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process', 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served)
    { }

    lemma lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process', 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served)
    { }
    
    lemma lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state    
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process', 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served)
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
            lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process',
                hn,
                sequence_proposer_duties_to_be_served,
                index_next_proposer_duty_to_be_served
            );
        }
        else
        { }
    } 

    lemma lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires pred_proposer_duty_is_from_dv_seq_of_proposer_duties_body(  
                        proposer_duty,
                        hn,
                        sequence_proposer_duties_to_be_served, 
                        index_next_proposer_duty_to_be_served
                    )
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process', 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served)
    { }

    lemma lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires dvc.latest_proposer_duty.isPresent()
    requires pred_proposer_duty_is_from_dv_seq_of_proposer_duties_body(  
                        proposer_duty,
                        hn,
                        sequence_proposer_duties_to_be_served, 
                        index_next_proposer_duty_to_be_served
                    )
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    dvc, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    dvc', 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served)
    { 
        var slot := proposer_duty.slot;
        var fork_version := bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, dvc.rs);
        var randao_share := 
            RandaoShare(
                proposer_duty := proposer_duty,
                slot := slot,
                signing_root := randao_reveal_signing_root,
                signature := randao_reveal_signature_share
            );
        var process_after_adding_randao_share :=
            dvc.(
                randao_shares_to_broadcast := dvc.randao_shares_to_broadcast[proposer_duty.slot := randao_share]
            );

        lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc',
            hn,
            sequence_proposer_duties_to_be_served,
            index_next_proposer_duty_to_be_served
        );
    }

    lemma lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires pred_proposer_duty_is_from_dv_seq_of_proposer_duties_body(  
                        proposer_duty,
                        hn,
                        sequence_proposer_duties_to_be_served, 
                        index_next_proposer_duty_to_be_served
                    )
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process', 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served)
    {        
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);

        lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty,
            hn,
            sequence_proposer_duties_to_be_served,
            index_next_proposer_duty_to_be_served
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
        lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process',
            hn,
            sequence_proposer_duties_to_be_served,
            index_next_proposer_duty_to_be_served
        );   
    }      

    lemma lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process', 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served)
    { }  

    lemma lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process', 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served)
    { }

    lemma lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process', 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served)
    { }  

    lemma lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process', 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served)
    { }  

    lemma lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process', 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served)
    { }    

    lemma lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)
    requires inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process)
    ensures inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process')
    { }
    
    lemma lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process)
    ensures inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process')
    { }

    lemma lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    requires inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process)
    ensures inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process')
    { }      

    lemma lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state    
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    requires inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process)
    ensures inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process')
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
            lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires proposer_duty in process.all_rcvd_duties
    requires inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process)
    ensures inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process')
    { 
        assert process.latest_proposer_duty.isPresent();
        assert process'.latest_proposer_duty.isPresent();
    }

    lemma lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires proposer_duty in dvc.all_rcvd_duties
    requires dvc.latest_proposer_duty.isPresent()
    requires inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(dvc)
    ensures inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(dvc')
    { 
        var slot := proposer_duty.slot;
        var fork_version := bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, dvc.rs);
        var randao_share := 
            RandaoShare(
                proposer_duty := proposer_duty,
                slot := slot,
                signing_root := randao_reveal_signing_root,
                signature := randao_reveal_signature_share
            );
        var process_after_adding_randao_share :=
            dvc.(
                randao_shares_to_broadcast := dvc.randao_shares_to_broadcast[proposer_duty.slot := randao_share]
            );

        lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc'
        );
    }

    lemma lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process)
    ensures inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);

        lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process)
    ensures inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process')
    { }  

    lemma lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process)
    ensures inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process')
    { }

    lemma lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process)
    ensures inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process')
    { }  

    lemma lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process)
    ensures inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process')
    { }  

    lemma lem_inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process)
    ensures inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process')
    { }      

    lemma lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process)
    ensures inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process')
    { }

    lemma lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(process)
    requires inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process)
    ensures inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process')
    { }      

    lemma lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(process)
    requires inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process)
    ensures inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process')
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
            lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires proposer_duty in process.all_rcvd_duties
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(process)
    requires inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process)
    ensures inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process')
    { 
        var slot := proposer_duty.slot;
        if slot in process.future_consensus_instances_on_blocks_already_decided.Keys 
        { }
        else 
        {
            lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body_f_start_consensus_if_can_construct_randao_share(
                process,
                process'
            );
        }
    }

    lemma lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires proposer_duty in dvc.all_rcvd_duties
    requires dvc.latest_proposer_duty.isPresent()
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(dvc)
    requires inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(dvc)
    ensures inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(dvc')
    { 
        var slot := proposer_duty.slot;
        var fork_version := bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, dvc.rs);
        var randao_share := 
            RandaoShare(
                proposer_duty := proposer_duty,
                slot := slot,
                signing_root := randao_reveal_signing_root,
                signature := randao_reveal_signature_share
            );
        var process_after_adding_randao_share :=
            dvc.(
                randao_shares_to_broadcast := dvc.randao_shares_to_broadcast[proposer_duty.slot := randao_share]
            );

        lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc'
        );
    }

    lemma lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process)
    ensures inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);

        lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process)
    ensures inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process')
    { }  

    lemma lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process)
    ensures inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process')
    { }

    lemma lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process)
    ensures inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process')
    { }  

    lemma lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process)
    ensures inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process')
    { }  

    lemma lem_inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process)
    ensures inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process')
    { }  

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process')
    { }

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process')
    { }

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(process)
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process')
    { }      

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(process)
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process')
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
            lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires proposer_duty in process.all_rcvd_duties
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(process)
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process')
    { 
        var slot := proposer_duty.slot;
        if slot in process.future_consensus_instances_on_blocks_already_decided.Keys 
        { }
        else 
        {
            lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_start_consensus_if_can_construct_randao_share(
                process,
                process'
            );
        }

    }

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires proposer_duty in dvc.all_rcvd_duties
    requires dvc.latest_proposer_duty.isPresent()
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(dvc)
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(dvc)
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(dvc')
    { 
        var slot := proposer_duty.slot;
        var fork_version := bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, dvc.rs);
        var randao_share := 
            RandaoShare(
                proposer_duty := proposer_duty,
                slot := slot,
                signing_root := randao_reveal_signing_root,
                signature := randao_reveal_signature_share
            );
        var process_after_adding_randao_share :=
            dvc.(
                randao_shares_to_broadcast := dvc.randao_shares_to_broadcast[proposer_duty.slot := randao_share]
            );

        lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc'
        );
    }

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);

        lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process')
    { }  

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process')
    { }

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process')
    { }  

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process')
    { }  

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    ensures inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process')
    { } 

     lemma lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_terminate_current_proposer_duty(
        dv: DVState,
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process)
    ensures inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process')
    { }

    lemma lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_start_consensus_if_can_construct_randao_share(
        dv: DVState,
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process)
    ensures inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process')
    { }  

    lemma lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_listen_for_randao_shares(
        dv: DVState,
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process)
    ensures inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process')
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
            assert inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process_with_new_randao_share);
            lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_start_consensus_if_can_construct_randao_share(
                dv,
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }    

    lemma lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_check_for_next_duty(
        dv: DVState,
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process)
    ensures inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process')
    { }

    lemma lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_broadcast_randao_share(
        dv: DVState,
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    requires inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process)
    ensures inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process')
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

        lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_check_for_next_duty(
            dv,
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_serve_proposer_duty(
        dv: DVState,
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process)
    ensures inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);

        lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_terminate_current_proposer_duty(
            dv,
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
        lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_broadcast_randao_share(
            dv,
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_block_consensus_decided(
        dv: DVState,
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process)
    ensures inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process')
    { } 

    lemma lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_listen_for_block_signature_shares(
        dv: DVState,
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires block_share in dv.block_share_network.allMessagesSent
    requires inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process)
    ensures inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process')
    { }

    lemma lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_listen_for_new_imported_blocks(
        dv: DVState,
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process)
    ensures inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process')
    { }  

    lemma lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_resend_randao_share(
        dv: DVState,
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process)
    ensures inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process')
    { }  

    lemma lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_resend_block_share(
        dv: DVState,
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process)
    ensures inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process')
    { }  

    lemma lem_inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    ensures process'.bn.submitted_blocks == process.bn.submitted_blocks      
    ensures process'.rcvd_block_shares == process.rcvd_block_shares
    { } 

    lemma lem_f_terminate_current_proposer_duty_unchanged_vars(
        s: DVCState,
        s': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(s)
    requires s' == f_terminate_current_proposer_duty(s)
    ensures s'.bn.submitted_blocks == s.bn.submitted_blocks
    ensures s'.rcvd_block_shares == s.rcvd_block_shares
    { }

    lemma lem_f_broadcast_randao_share_unchanged_vars(
        s: DVCState,
        proposer_duty: ProposerDuty,
        s': DVCState
    )  
    requires f_broadcast_randao_share.requires(s, proposer_duty)
    requires s' == f_broadcast_randao_share(s, proposer_duty).state
    ensures s'.bn.submitted_blocks == s.bn.submitted_blocks      
    ensures s'.rcvd_block_shares == s.rcvd_block_shares
    ensures f_broadcast_randao_share(s, proposer_duty).outputs.submitted_blocks == {}
    ensures f_serve_proposer_duty(s, proposer_duty).outputs.sent_block_shares == {}
    { }

    lemma lem_f_serve_proposer_duty_unchanged_vars(
        s: DVCState,
        proposer_duty: ProposerDuty,
        s': DVCState
    )  
    requires f_serve_proposer_duty.requires(s, proposer_duty)
    requires s' == f_serve_proposer_duty(s, proposer_duty).state
    ensures s'.bn.submitted_blocks == s.bn.submitted_blocks      
    ensures s'.rcvd_block_shares == s.rcvd_block_shares
    ensures f_serve_proposer_duty(s, proposer_duty).outputs.submitted_blocks == {}
    ensures f_serve_proposer_duty(s, proposer_duty).outputs.sent_block_shares == {}
    { 
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(s);

        lem_f_terminate_current_proposer_duty_unchanged_vars(
            s,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
        lem_f_broadcast_randao_share_unchanged_vars(
            process_after_receiving_duty,
            proposer_duty,
            s'
        );   
    }

    lemma lem_f_listen_for_randao_shares_unchanged_vars(
        s: DVCState,
       randao_share: RandaoShare,
        s': DVCState
    )  
    requires f_listen_for_randao_shares.requires(s, randao_share)
    requires s' == f_listen_for_randao_shares(s, randao_share).state
    ensures s'.bn.submitted_blocks == s.bn.submitted_blocks      
    ensures s'.rcvd_block_shares == s.rcvd_block_shares
    ensures f_listen_for_randao_shares(s, randao_share).outputs.submitted_blocks == {}
    ensures f_listen_for_randao_shares(s, randao_share).outputs.sent_block_shares == {}
    { }

    lemma lem_f_listen_for_block_signature_shares_unchanged_vars(
        s: DVCState,
        block_share: SignedBeaconBlock,
        s': DVCState
    )  
    requires f_listen_for_block_signature_shares.requires(s, block_share)
    requires s' == f_listen_for_block_signature_shares(s, block_share).state
    ensures f_listen_for_block_signature_shares(s, block_share).outputs.sent_block_shares == {}
    { }

    lemma lem_f_check_for_next_duty_unchanged_dvc_vars(
        s: DVCState,
        proposer_duty: ProposerDuty,
        s': DVCState
    )
    requires f_check_for_next_duty.requires(s, proposer_duty)
    requires s' == f_check_for_next_duty(s, proposer_duty).state
    ensures s'.bn.submitted_blocks == s.bn.submitted_blocks
    ensures s'.rcvd_block_shares == s.rcvd_block_shares
    ensures f_check_for_next_duty(s, proposer_duty).outputs == getEmptyOuputs()
    { }

    lemma lem_f_block_consensus_decided_unchanged_dvc_vars(
        s: DVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock,        
        s': DVCState
    )
    requires f_block_consensus_decided.requires(s, id, decided_beacon_block)
    requires s' == f_block_consensus_decided(s, id, decided_beacon_block).state
    ensures s'.bn.submitted_blocks == s.bn.submitted_blocks
    ensures s'.rcvd_block_shares == s.rcvd_block_shares
    { } 

    lemma lem_f_listen_for_new_imported_blocks_unchanged_dvc_vars(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(s, block)
    requires s' == f_listen_for_new_imported_blocks(s, block).state
    ensures s'.bn.submitted_blocks == s.bn.submitted_blocks
    ensures s'.rcvd_block_shares.Keys <= s.rcvd_block_shares.Keys
    ensures forall k | k in s'.rcvd_block_shares.Keys :: s'.rcvd_block_shares[k] == s.rcvd_block_shares[k]
    ensures f_listen_for_new_imported_blocks(s, block).outputs == getEmptyOuputs()
    ensures f_listen_for_new_imported_blocks(s, block).outputs.sent_block_shares == {}
    { }  

    lemma lem_f_listen_for_block_signature_shares_unchanged_dvc_vars(
        s: DVCState,
        block_share: SignedBeaconBlock,
        s': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(s, block_share)
    requires s' == f_listen_for_block_signature_shares(s, block_share).state    
    ensures s'.block_consensus_engine_state == s.block_consensus_engine_state
    ensures s'.block_consensus_engine_state.block_slashing_db_hist == s.block_consensus_engine_state.block_slashing_db_hist
    ensures s'.latest_proposer_duty == s.latest_proposer_duty
    ensures s'.current_proposer_duty == s.current_proposer_duty
    ensures s'.block_slashing_db == s.block_slashing_db
    ensures s'.future_consensus_instances_on_blocks_already_decided == s.future_consensus_instances_on_blocks_already_decided
    { }

    lemma lem_f_resend_block_share_unchanged_dvc_vars(
        s: DVCState,
        s': DVCState
    )
    requires f_resend_block_share.requires(s)
    requires s' == f_resend_block_share(s).state    
    ensures s'.block_consensus_engine_state == s.block_consensus_engine_state
    ensures s'.block_consensus_engine_state.block_slashing_db_hist == s.block_consensus_engine_state.block_slashing_db_hist
    ensures s'.latest_proposer_duty == s.latest_proposer_duty
    ensures s'.current_proposer_duty == s.current_proposer_duty
    ensures s'.block_slashing_db == s.block_slashing_db
    ensures s'.future_consensus_instances_on_blocks_already_decided == s.future_consensus_instances_on_blocks_already_decided
    { }   

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process)
    ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process')
    { }

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process)
    ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process')
    { }

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process)
    ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process')
    { 
        if && process.current_proposer_duty.isPresent()
           && process.current_proposer_duty.safe_get().slot in process.rcvd_randao_shares
        {
            var proposer_duty := process.current_proposer_duty.safe_get();
            var all_rcvd_randao_sig := 
                    set randao_share | randao_share in process.rcvd_randao_shares[
                                                process.current_proposer_duty.safe_get().slot]
                                                    :: randao_share.signature;                
            var constructed_randao_reveal := process.construct_complete_signed_randao_reveal(all_rcvd_randao_sig);
            if && constructed_randao_reveal.isPresent()  
               && proposer_duty.slot !in process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys 
            {
                forall cid | cid in process'.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks
                ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_body(process', cid)
                {
                    if cid in process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks
                    {
                        assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_body(process', cid);
                    }
                    else
                    {
                        assert cid == proposer_duty.slot;

                        var constructed_complete_randao_reveal := constructed_randao_reveal.safe_get();
                        var validityPredicate := ((block: BeaconBlock)  => 
                                            ci_decision_is_valid_beacon_block(
                                                process.block_slashing_db, 
                                                block, 
                                                process.current_proposer_duty.safe_get(),
                                                constructed_complete_randao_reveal
                                            )); 

                        assert  process'.block_consensus_engine_state ==
                                startBlockConsensusInstance(
                                    process.block_consensus_engine_state,
                                    proposer_duty.slot,
                                    proposer_duty,
                                    process.block_slashing_db,
                                    constructed_complete_randao_reveal
                                );

                                    
                        var bcvc := 
                            BlockConsensusValidityCheckState(
                                proposer_duty := proposer_duty,
                                randao_reveal := constructed_complete_randao_reveal,
                                validityPredicate := (bb: BeaconBlock) => ci_decision_is_valid_beacon_block(process.block_slashing_db, bb, proposer_duty, constructed_complete_randao_reveal)
                            );

                        assert bcvc == process'.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid];
                        assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(
                                    cid, 
                                    proposer_duty, 
                                    process.block_slashing_db, 
                                    bcvc.randao_reveal,
                                    bcvc.validityPredicate                                    
                                );
                        assert inv_existing_block_slashing_db_for_sent_vp(cid, proposer_duty, bcvc.randao_reveal, bcvc.validityPredicate);
                        assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_body(process', cid);
                    }
                }
            }
            else
            { }
        }
        else
        { }        
    }      

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process)
    ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process')
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
            lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_updateBlockConsensusInstanceValidityCheckHelper(
        m: map<Slot, BlockConsensusValidityCheckState>,
        new_block_slashing_db: set<SlashingDBBlock>,
        m': map<Slot, BlockConsensusValidityCheckState>
    )
    requires m' == updateBlockConsensusInstanceValidityCheckHelper(m, new_block_slashing_db)
    requires forall k | k in m :: inv_existing_block_slashing_db_for_sent_vp(k, m[k].proposer_duty, m[k].randao_reveal, m[k].validityPredicate)
    ensures forall k | k in m' :: inv_existing_block_slashing_db_for_sent_vp(k, m'[k].proposer_duty, m'[k].randao_reveal, m'[k].validityPredicate)
    {
        forall k | k in  m
        ensures k in m'
        {
            lemmaMapKeysHasOneEntryInItems(m, k);
            assert k in m';
        }

        assert m.Keys == m'.Keys;

        forall k | k in m'
        ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(
                    k, 
                    m'[k].proposer_duty, 
                    new_block_slashing_db, 
                    m'[k].randao_reveal,
                    m'[k].validityPredicate
                );
        {
            assert  m'[k] 
                    == 
                    m[k].(
                        validityPredicate := (block: BeaconBlock) => ci_decision_is_valid_beacon_block(
                                                                            new_block_slashing_db, 
                                                                            block, 
                                                                            m[k].proposer_duty, 
                                                                            m[k].randao_reveal)
                    );
            assert  && m'[k].proposer_duty == m[k].proposer_duty
                    && m'[k].randao_reveal == m[k].randao_reveal
                    ;
            assert  inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(
                        k, 
                        m'[k].proposer_duty, 
                        new_block_slashing_db, 
                        m'[k].randao_reveal,
                        m'[k].validityPredicate
                    );
        }
    }

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process)
    ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process')
    { 
        var slot := proposer_duty.slot;
        if slot in process.future_consensus_instances_on_blocks_already_decided 
        {
            var block := process.future_consensus_instances_on_blocks_already_decided[slot];                
            var new_block_slashing_db := 
                f_update_block_slashing_db(process.block_slashing_db, block);            
            var new_process
                := 
                process.(
                    current_proposer_duty := None,
                    latest_proposer_duty := Some(proposer_duty),
                    future_consensus_instances_on_blocks_already_decided := process.future_consensus_instances_on_blocks_already_decided - {slot},
                    block_slashing_db := new_block_slashing_db,
                    block_consensus_engine_state := updateBlockConsensusInstanceValidityCheck(
                            process.block_consensus_engine_state,
                            new_block_slashing_db
                    )     
                );

            lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_updateBlockConsensusInstanceValidityCheckHelper(
                    process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks,
                    new_process.block_slashing_db,
                    new_process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks
            );
        }
        else
        {
            lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_start_consensus_if_can_construct_randao_share(
                process,
                process'
            );
        }
    }

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires dvc.latest_proposer_duty.isPresent()
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(dvc)
    ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(dvc')
    { 
        var slot := proposer_duty.slot;
        var fork_version := bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, dvc.rs);
        var randao_share := 
            RandaoShare(
                proposer_duty := proposer_duty,
                slot := slot,
                signing_root := randao_reveal_signing_root,
                signature := randao_reveal_signature_share
            );
        var process_after_adding_randao_share :=
            dvc.(
                randao_shares_to_broadcast := dvc.randao_shares_to_broadcast[proposer_duty.slot := randao_share]
            );

        lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc'
        );
    }

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process)
    ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        
        lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    requires inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process)
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process)
    ensures  inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process')
    { 
        if && process.current_proposer_duty.isPresent()
           && process.current_proposer_duty.safe_get().slot == block.slot
           && id == block.slot
        {
            var new_block_slashing_db := f_update_block_slashing_db(process.block_slashing_db, block);
            var new_block_consensus_engine_state := 
                updateBlockConsensusInstanceValidityCheck(
                        process.block_consensus_engine_state,
                        new_block_slashing_db
                );
            var new_active_consensus_instances_on_beacon_blocks := 
                updateBlockConsensusInstanceValidityCheckHelper(
                    process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks,
                    new_block_slashing_db
                );

            assert  new_active_consensus_instances_on_beacon_blocks.Keys
                    <=
                    process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys
                    ;
              
            forall cid | cid in process'.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks
            ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_body(process', cid)        
            {
                assert  cid in process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks;
                assert  process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid].proposer_duty
                        ==
                        process'.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid].proposer_duty
                        ;
                assert  process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid].randao_reveal
                        ==
                        process'.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid].randao_reveal
                        ;

                var vp := process'.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid].validityPredicate;
                var duty: ProposerDuty := new_active_consensus_instances_on_beacon_blocks[cid].proposer_duty;
                var randao_reveal: BLSSignature := new_active_consensus_instances_on_beacon_blocks[cid].randao_reveal;                    
                
                assert  new_block_slashing_db in process'.block_consensus_engine_state.block_slashing_db_hist[cid][vp];
                assert  duty.slot == cid;
                assert  vp == (block: BeaconBlock) => ci_decision_is_valid_beacon_block(new_block_slashing_db, block, duty, randao_reveal);
                assert  inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(
                            cid,
                            duty,
                            new_block_slashing_db,
                            randao_reveal,
                            vp
                        );
                assert  inv_existing_block_slashing_db_for_sent_vp(
                            cid,
                            duty,
                            randao_reveal,
                            vp
                        );
            }           
        }
        else
        {
            assert inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process');
        }            
    }  

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process)
    ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process')
    { }

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process)
    ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process')
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
        
        assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process_after_stopping_consensus_instance);

        if process_after_stopping_consensus_instance.current_proposer_duty.isPresent() && process_after_stopping_consensus_instance.current_proposer_duty.safe_get().slot in consensus_instances_on_blocks_already_decided 
        {
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

            lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_updateBlockConsensusInstanceValidityCheckHelper(
                    process_after_stopping_consensus_instance.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks,
                    process_after_updating_validity_check.block_slashing_db,
                    process_after_updating_validity_check.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks
            );
        }
        else
        {
            assert inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process');
        }
    }  

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process)
    ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process')
    { }  

    lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process)
    ensures inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(process')
    { }  

    lemma lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(s)
    ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(s')
    { }

    lemma lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process)
    ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process')
    { }

    lemma lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(process)
    requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process)
    ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process')
    { }      

    lemma lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(process)
    requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process)
    ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process')
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
            lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process)
    requires proposer_duty in process.all_rcvd_duties
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(process)
    requires inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process)
    ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process')
    { 
        var slot := proposer_duty.slot;
        if slot in process.future_consensus_instances_on_blocks_already_decided 
        {
            var block := process.future_consensus_instances_on_blocks_already_decided[slot];                
            var new_block_slashing_db := 
                f_update_block_slashing_db(process.block_slashing_db, block);      
            var new_active_consensus_instances_on_beacon_blocks := 
                updateBlockConsensusInstanceValidityCheckHelper(
                    process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks,
                    new_block_slashing_db
                );      
            assert  new_active_consensus_instances_on_beacon_blocks.Keys
                    <=
                    process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys
                    ;

            var new_block_slashing_db_hist := 
                updateBlockSlashingDBHist(
                    process.block_consensus_engine_state.block_slashing_db_hist,
                    new_active_consensus_instances_on_beacon_blocks,
                    new_block_slashing_db
                );
            assert  new_block_slashing_db_hist.Keys 
                    ==
                    process.block_consensus_engine_state.block_slashing_db_hist.Keys + new_active_consensus_instances_on_beacon_blocks.Keys
                    ;
            assert  process'.block_consensus_engine_state.block_slashing_db_hist
                    ==
                    new_block_slashing_db_hist
                    ;
            assert  new_active_consensus_instances_on_beacon_blocks.Keys
                    <=
                    process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys
                    ;
            
            forall k: Slot | k in process'.block_consensus_engine_state.block_slashing_db_hist.Keys 
            ensures  exists duty: ProposerDuty :: 
                            && duty in process'.all_rcvd_duties
                            && duty.slot == k
                            ;
            {
                if k in process.block_consensus_engine_state.block_slashing_db_hist.Keys
                {
                    var duty: ProposerDuty :| && duty in process.all_rcvd_duties
                                              && duty.slot == k
                                              ;
                    assert process.all_rcvd_duties <= process'.all_rcvd_duties;
                    assert exists duty: ProposerDuty :: 
                                && duty in process'.all_rcvd_duties
                                && duty.slot == k
                                ;
                }
                else
                {
                    assert k in new_active_consensus_instances_on_beacon_blocks.Keys;
                    assert k in process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys;
                    var rcvd_duty: ProposerDuty :|  && rcvd_duty in process.all_rcvd_duties
                                                    && rcvd_duty.slot == k
                                                    ;
                    assert process.all_rcvd_duties <= process'.all_rcvd_duties;
                    assert exists duty: ProposerDuty :: 
                                && duty in process'.all_rcvd_duties
                                && duty.slot == k
                                ;
                }
            }

            assert inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process');
        }          
        else 
        {
            lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_start_consensus_if_can_construct_randao_share(
                process,
                process'
            );
        }  
    }

    lemma lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires dvc.latest_proposer_duty.isPresent()
    requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(dvc)
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(dvc)
    requires inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(dvc)
    requires proposer_duty in dvc.all_rcvd_duties
    ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(dvc')
    { 
        var slot := proposer_duty.slot;
        var fork_version := bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, dvc.rs);
        var randao_share := 
            RandaoShare(
                proposer_duty := proposer_duty,
                slot := slot,
                signing_root := randao_reveal_signing_root,
                signature := randao_reveal_signature_share
            );
        var process_after_adding_randao_share :=
            dvc.(
                randao_shares_to_broadcast := dvc.randao_shares_to_broadcast[proposer_duty.slot := randao_share]
            );

        lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc'
        );
    }

    lemma lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process)
    requires inv_current_proposer_duty_is_a_rcvd_duty_body(process)
    requires inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process)
    ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        
        lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)
    requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process)
    ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process')
    { 
        if && process.current_proposer_duty.isPresent()
           && process.current_proposer_duty.safe_get().slot == block.slot
           && id == block.slot
        {
            var new_block_slashing_db := 
                f_update_block_slashing_db(process.block_slashing_db, block);      
            var new_active_consensus_instances_on_beacon_blocks := 
                updateBlockConsensusInstanceValidityCheckHelper(
                    process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks,
                    new_block_slashing_db
                );      
            assert  new_active_consensus_instances_on_beacon_blocks.Keys
                    <=
                    process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys
                    ;

            var new_block_slashing_db_hist := 
                updateBlockSlashingDBHist(
                    process.block_consensus_engine_state.block_slashing_db_hist,
                    new_active_consensus_instances_on_beacon_blocks,
                    new_block_slashing_db
                );
            assert  new_block_slashing_db_hist.Keys 
                    ==
                    process.block_consensus_engine_state.block_slashing_db_hist.Keys + new_active_consensus_instances_on_beacon_blocks.Keys
                    ;
            assert  process'.block_consensus_engine_state.block_slashing_db_hist
                    ==
                    new_block_slashing_db_hist
                    ;
            assert  new_active_consensus_instances_on_beacon_blocks.Keys
                    <=
                    process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys
                    ;
            
            forall k: Slot | k in process'.block_consensus_engine_state.block_slashing_db_hist.Keys 
            ensures  exists duty: ProposerDuty :: 
                            && duty in process'.all_rcvd_duties
                            && duty.slot == k
                            ;
            {
                if k in process.block_consensus_engine_state.block_slashing_db_hist.Keys
                {
                    var duty: ProposerDuty :| && duty in process.all_rcvd_duties
                                              && duty.slot == k
                                              ;
                    assert process.all_rcvd_duties <= process'.all_rcvd_duties;
                    assert exists duty: ProposerDuty :: 
                                && duty in process'.all_rcvd_duties
                                && duty.slot == k
                                ;
                }
                else
                {
                    assert k in new_active_consensus_instances_on_beacon_blocks.Keys;
                    assert k in process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys;
                    assert k in process.block_consensus_engine_state.block_slashing_db_hist.Keys;
                    var rcvd_duty: ProposerDuty :|  && rcvd_duty in process.all_rcvd_duties
                                                    && rcvd_duty.slot == k
                                                    ;
                    assert process.all_rcvd_duties <= process'.all_rcvd_duties;
                    assert exists duty: ProposerDuty :: 
                                && duty in process'.all_rcvd_duties
                                && duty.slot == k
                                ;
                }
            }

            assert inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process');
        }          
        else 
        {
            
        } 
    }  

    lemma lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process)
    ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process')
    { }

    lemma lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(process)
    requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process)
    ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process')
    { }  

    lemma lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process)
    ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process')
    { }  

    lemma lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process)
    ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process')
    { }  

    lemma lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_f_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    requires inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(s)
    ensures inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(s')
    { }

    lemma lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process)
    ensures inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process')
    { }

    lemma lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process)
    ensures inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process')
    { }      

    lemma lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process)
    ensures inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process')
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
            lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    requires inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process)
    ensures inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process')
    { }

    lemma lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(dvc)
    requires dvc.latest_proposer_duty.isPresent()
    requires inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(dvc)
    ensures inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(dvc')
    { 
        var slot := proposer_duty.slot;
        var fork_version := bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, dvc.rs);
        var randao_share := 
            RandaoShare(
                proposer_duty := proposer_duty,
                slot := slot,
                signing_root := randao_reveal_signing_root,
                signature := randao_reveal_signature_share
            );
        var process_after_adding_randao_share :=
            dvc.(
                randao_shares_to_broadcast := dvc.randao_shares_to_broadcast[proposer_duty.slot := randao_share]
            );

        lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc'
        );
    }

    lemma lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    requires inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process)
    ensures inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        
        lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_updateBlockConsensusInstanceValidityCheckHelper(
        m: map<Slot, BlockConsensusValidityCheckState>,
        new_block_slashing_db: set<SlashingDBBlock>,
        r: map<Slot, BlockConsensusValidityCheckState>
    )
    requires r == updateBlockConsensusInstanceValidityCheckHelper(m, new_block_slashing_db)
    requires (  forall k: Slot | k in m.Keys :: m[k].proposer_duty.slot == k );
    ensures  (  forall k: Slot | k in r.Keys :: r[k].proposer_duty.slot == k );
    {

    }

    lemma lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    requires inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process)
    ensures inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process')
    { 
        if && process.current_proposer_duty.isPresent()
           && process.current_proposer_duty.safe_get().slot == block.slot
           && id == block.slot
        {
            var new_block_slashing_db := f_update_block_slashing_db(process.block_slashing_db, block);
            var new_block_consensus_engine_state := 
                updateBlockConsensusInstanceValidityCheck(
                        process.block_consensus_engine_state,
                        new_block_slashing_db
                );
            var new_active_consensus_instances_on_beacon_blocks := 
                updateBlockConsensusInstanceValidityCheckHelper(
                    process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks,
                    new_block_slashing_db
                );

            lem_inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body_updateBlockConsensusInstanceValidityCheckHelper(
                process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks,
                new_block_slashing_db,
                new_active_consensus_instances_on_beacon_blocks
            );
            assert  (  forall k: Slot | k in new_active_consensus_instances_on_beacon_blocks.Keys 
                            :: 
                            new_active_consensus_instances_on_beacon_blocks[k].proposer_duty.slot == k 
                    );
            
            var new_block_slashing_db_hist := 
                updateBlockSlashingDBHist(
                    process.block_consensus_engine_state.block_slashing_db_hist,
                    new_active_consensus_instances_on_beacon_blocks,
                    new_block_slashing_db
                );

            assert  process'.block_consensus_engine_state.block_slashing_db_hist
                    ==
                    new_block_slashing_db_hist
                    ;

            assert  process.block_consensus_engine_state.block_slashing_db_hist.Keys + new_active_consensus_instances_on_beacon_blocks.Keys 
                    == 
                    process'.block_consensus_engine_state.block_slashing_db_hist.Keys
                    ;
            
            forall s: Slot, vp: BeaconBlock -> bool |
                ( && s in process'.block_consensus_engine_state.block_slashing_db_hist.Keys
                  && vp in process'.block_consensus_engine_state.block_slashing_db_hist[s].Keys
                )
            ensures
                ( exists db: set<SlashingDBBlock>, duty: ProposerDuty, randao_reveal: BLSSignature ::
                        && duty.slot == s
                        && db in process'.block_consensus_engine_state.block_slashing_db_hist[s][vp]
                        && vp == (block: BeaconBlock) => ci_decision_is_valid_beacon_block(db, block, duty, randao_reveal)
                );
            {
                if  s in process.block_consensus_engine_state.block_slashing_db_hist.Keys                    
                {
                    if  vp in process.block_consensus_engine_state.block_slashing_db_hist[s]
                    {
                        assert  ( exists db: set<SlashingDBBlock>, duty: ProposerDuty, randao_reveal: BLSSignature ::
                                    && duty.slot == s
                                    && db in process'.block_consensus_engine_state.block_slashing_db_hist[s][vp]
                                    && vp == (block: BeaconBlock) => ci_decision_is_valid_beacon_block(db, block, duty, randao_reveal)
                            );
                    }
                    else
                    {
                        assert vp == new_active_consensus_instances_on_beacon_blocks[s].validityPredicate;
                        assert new_block_slashing_db in process'.block_consensus_engine_state.block_slashing_db_hist[s][vp];

                        var duty: ProposerDuty := new_active_consensus_instances_on_beacon_blocks[s].proposer_duty;
                        var randao_reveal: BLSSignature := new_active_consensus_instances_on_beacon_blocks[s].randao_reveal;                    
                        assert duty.slot == s;
                        assert vp == (block: BeaconBlock) => ci_decision_is_valid_beacon_block(new_block_slashing_db, block, duty, randao_reveal);

                        assert  ( exists db: set<SlashingDBBlock>, duty: ProposerDuty, randao_reveal: BLSSignature ::
                                        && duty.slot == s
                                        && db in process'.block_consensus_engine_state.block_slashing_db_hist[s][vp]
                                        && vp == (block: BeaconBlock) => ci_decision_is_valid_beacon_block(db, block, duty, randao_reveal)
                                );
                    }
                    
                }
                else
                {
                    assert s in new_active_consensus_instances_on_beacon_blocks.Keys;
                    assert vp == new_active_consensus_instances_on_beacon_blocks[s].validityPredicate;

                    var hist := process.block_consensus_engine_state.block_slashing_db_hist;
                    var new_hist := process'.block_consensus_engine_state.block_slashing_db_hist;
                    var hist_s := getOrDefault(hist, s, map[]);
                    var hist_s_vp := getOrDefault(hist_s, vp, {}) + {new_block_slashing_db};
                    assert hist_s == map[];
                    assert hist_s_vp == {new_block_slashing_db};
                    assert new_block_slashing_db in process'.block_consensus_engine_state.block_slashing_db_hist[s][vp];

                    var duty: ProposerDuty := new_active_consensus_instances_on_beacon_blocks[s].proposer_duty;
                    var randao_reveal: BLSSignature := new_active_consensus_instances_on_beacon_blocks[s].randao_reveal;                    
                    assert duty.slot == s;
                    assert vp == (block: BeaconBlock) => ci_decision_is_valid_beacon_block(new_block_slashing_db, block, duty, randao_reveal);

                    assert  ( exists db: set<SlashingDBBlock>, duty: ProposerDuty, randao_reveal: BLSSignature ::
                                    && duty.slot == s
                                    && db in process'.block_consensus_engine_state.block_slashing_db_hist[s][vp]
                                    && vp == (block: BeaconBlock) => ci_decision_is_valid_beacon_block(db, block, duty, randao_reveal)
                            );
                }

            }            
        }
        else
        {
            assert inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process');
        }            
    }  

    lemma lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process)
    ensures inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process')
    { }

    lemma lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    requires inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process)
    ensures inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process')
    { }  

    lemma lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process)
    ensures inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process')
    { }  

    lemma lem_inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process)
    ensures inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(process')
    { }  

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body_f_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(s)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(s')
    { }

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(process)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(process')
    { }

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(process)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(process')
    { }      

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(process)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(process')
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
            lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(process)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(process')
    { }

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires dvc.latest_proposer_duty.isPresent()
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(dvc)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(dvc')
    { 
        var slot := proposer_duty.slot;
        var fork_version := bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, dvc.rs);
        var randao_share := 
            RandaoShare(
                proposer_duty := proposer_duty,
                slot := slot,
                signing_root := randao_reveal_signing_root,
                signature := randao_reveal_signature_share
            );
        var process_after_adding_randao_share :=
            dvc.(
                randao_shares_to_broadcast := dvc.randao_shares_to_broadcast[proposer_duty.slot := randao_share]
            );

        lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc'
        );
    }

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(process)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        
        lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );  
    } 

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(process)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(process')
    { }  

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(process)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(process')
    { }

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(process)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(process')
    { }  

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(process)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(process')
    { }  

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(process)
    ensures inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(process')
    { }  

    lemma lem_inv_block_slashing_db_hist_is_monotonic_body_f_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    ensures inv_block_slashing_db_hist_is_monotonic_body(s, s')
    { }

    lemma lem_inv_block_slashing_db_hist_is_monotonic_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    ensures inv_block_slashing_db_hist_is_monotonic_body(process, process')
    { }

    lemma lem_inv_block_slashing_db_hist_is_monotonic_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    ensures inv_block_slashing_db_hist_is_monotonic_body(process, process')
    { }    

    lemma lem_inv_block_slashing_db_hist_is_monotonic_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    ensures inv_block_slashing_db_hist_is_monotonic_body(process, process')
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
            lem_inv_block_slashing_db_hist_is_monotonic_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_block_slashing_db_hist_is_monotonic_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    ensures inv_block_slashing_db_hist_is_monotonic_body(process, process')
    { }

    lemma lem_inv_block_slashing_db_hist_is_monotonic_body_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires dvc.latest_proposer_duty.isPresent()
    ensures inv_block_slashing_db_hist_is_monotonic_body(dvc, dvc')
    { 
        var slot := proposer_duty.slot;
        var fork_version := bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, dvc.rs);
        var randao_share := 
            RandaoShare(
                proposer_duty := proposer_duty,
                slot := slot,
                signing_root := randao_reveal_signing_root,
                signature := randao_reveal_signature_share
            );
        var process_after_adding_randao_share :=
            dvc.(
                randao_shares_to_broadcast := dvc.randao_shares_to_broadcast[proposer_duty.slot := randao_share]
            );

        lem_inv_block_slashing_db_hist_is_monotonic_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc'
        );
    }

    lemma lem_inv_block_slashing_db_hist_is_monotonic_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    ensures inv_block_slashing_db_hist_is_monotonic_body(process, process')
    {
         var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        
        lem_inv_block_slashing_db_hist_is_monotonic_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_block_slashing_db_hist_is_monotonic_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_block_slashing_db_hist_is_monotonic_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    ensures inv_block_slashing_db_hist_is_monotonic_body(process, process')
    { }  

    lemma lem_inv_block_slashing_db_hist_is_monotonic_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    ensures inv_block_slashing_db_hist_is_monotonic_body(process, process')
    { }

    lemma lem_inv_block_slashing_db_hist_is_monotonic_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    ensures inv_block_slashing_db_hist_is_monotonic_body(process, process')
    { }  

    lemma lem_inv_block_slashing_db_hist_is_monotonic_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    ensures inv_block_slashing_db_hist_is_monotonic_body(process, process')
    { }  

    lemma lem_inv_block_slashing_db_hist_is_monotonic_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    ensures inv_block_slashing_db_hist_is_monotonic_body(process, process')
    { }  

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process)
    requires inv_latest_served_duty_is_a_rcvd_duty_body(process)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
    { 
        if && process.current_proposer_duty.isPresent()
           && process.current_proposer_duty.safe_get().slot in process.rcvd_randao_shares
        {
            var proposer_duty := process.current_proposer_duty.safe_get();
            var all_rcvd_randao_sig := 
                    set randao_share | randao_share in process.rcvd_randao_shares[
                                                process.current_proposer_duty.safe_get().slot]
                                                    :: randao_share.signature;                
            var constructed_randao_reveal := process.construct_complete_signed_randao_reveal(all_rcvd_randao_sig);
            if && constructed_randao_reveal.isPresent()  
               && proposer_duty.slot !in process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys 
            {
                var slot := process.latest_proposer_duty.safe_get().slot;
                var validityPredicate := ((block: BeaconBlock)  => 
                                            ci_decision_is_valid_beacon_block(
                                                process.block_slashing_db, 
                                                block, 
                                                process.current_proposer_duty.safe_get(),
                                                constructed_randao_reveal.safe_get()));      
                var new_block_consensus_engine_state := 
                    startBlockConsensusInstance(
                            process.block_consensus_engine_state,
                            proposer_duty.slot,
                            proposer_duty,
                            process.block_slashing_db,
                            constructed_randao_reveal.safe_get()
                    );  
                assert  new_block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys    
                        ==
                        process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys + {slot}
                        ;
                assert  process'.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys
                        ==
                        process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys + {slot}
                        ;
                assert  process.current_proposer_duty.safe_get()
                        == 
                        process'.current_proposer_duty.safe_get()
                        ;

                lem_inv_available_current_proposer_duty_is_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
                    process,
                    process'
                );
                assert  && process.latest_proposer_duty.isPresent()
                        && process'.latest_proposer_duty.isPresent()
                        ;
                assert  process.latest_proposer_duty.safe_get()
                        == 
                        process'.latest_proposer_duty.safe_get()
                        ;

                forall s: Slot | s in process'.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys
                ensures s <= slot;
                {
                    if  s in process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys
                    {
                        assert s <= slot;
                    }
                    else
                    {

                    }
                }
            }
            else 
            {
                assert inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process'); 
            }            
        }
        else
        {
            assert inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process');
        }
            
    }      

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state    
    requires inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process)
    requires inv_latest_served_duty_is_a_rcvd_duty_body(process)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
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
            lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process)
    requires inv_latest_served_duty_is_a_rcvd_duty_body(process)
    requires proposer_duty in process.all_rcvd_duties
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    requires inv_slots_of_active_consensus_instances_are_lower_than_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
    { 
        var slot := proposer_duty.slot;
        if slot in process.future_consensus_instances_on_blocks_already_decided.Keys
        {            
            var block := process.future_consensus_instances_on_blocks_already_decided[slot];                
            var new_block_slashing_db := 
                f_update_block_slashing_db(process.block_slashing_db, block);            
            var new_process
                := 
                process.(
                    current_proposer_duty := None,
                    latest_proposer_duty := Some(proposer_duty),
                    future_consensus_instances_on_blocks_already_decided := process.future_consensus_instances_on_blocks_already_decided - {slot},
                    block_slashing_db := new_block_slashing_db,
                    block_consensus_engine_state := updateBlockConsensusInstanceValidityCheck(
                            process.block_consensus_engine_state,
                            new_block_slashing_db
                    
                    )     
                );

        }
        else 
        {
            lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
                process,
                process'
            );
        }
            
    }

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process)
    requires inv_latest_served_duty_is_a_rcvd_duty_body(process)
    requires proposer_duty in process.all_rcvd_duties
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    requires inv_slots_of_active_consensus_instances_are_lower_than_the_slot_of_latest_proposer_duty_body(process)
    requires process.latest_proposer_duty.isPresent()
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
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

        lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    requires inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(process)
    requires inv_latest_served_duty_is_a_rcvd_duty_body(process)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    requires inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty_body(process, proposer_duty)    
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        
        lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);

        assert  inv_slots_of_active_consensus_instances_are_lower_than_the_slot_of_latest_proposer_duty_body(process_after_receiving_duty);
       
        lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );
    } 

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
    { }  
}