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
        var process_after_receiving_duty := 
            dvc.(all_rcvd_duties := dvc.all_rcvd_duties + {proposer_duty});

        var process_after_stopping_active_consensus_instance := 
            f_terminate_current_proposer_duty(process_after_receiving_duty);

        
        lem_updated_all_rcvd_duties_f_terminate_current_proposer_duty(
            process_after_receiving_duty,
            process_after_stopping_active_consensus_instance
        );

        lem_updated_all_rcvd_duties_f_broadcast_randao_share(
            process_after_stopping_active_consensus_instance,
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

    lemma lem_inv_current_proposer_duty_is_rcvd_duty_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_current_proposer_duty_is_rcvd_duty_body(process)
    ensures inv_current_proposer_duty_is_rcvd_duty_body(process')
    { }

    lemma lem_inv_current_proposer_duty_is_rcvd_duty_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_current_proposer_duty_is_rcvd_duty_body(process)
    ensures inv_current_proposer_duty_is_rcvd_duty_body(process')
    { }      

    lemma lem_inv_current_proposer_duty_is_rcvd_duty_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state    
    requires inv_current_proposer_duty_is_rcvd_duty_body(process)
    ensures inv_current_proposer_duty_is_rcvd_duty_body(process')
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
            lem_inv_current_proposer_duty_is_rcvd_duty_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_current_proposer_duty_is_rcvd_duty_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires proposer_duty in process.all_rcvd_duties
    requires inv_current_proposer_duty_is_rcvd_duty_body(process)
    ensures inv_current_proposer_duty_is_rcvd_duty_body(process')
    { }

    lemma lem_inv_current_proposer_duty_is_rcvd_duty_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires proposer_duty in dvc.all_rcvd_duties
    requires inv_current_proposer_duty_is_rcvd_duty_body(dvc)
    ensures inv_current_proposer_duty_is_rcvd_duty_body(dvc')
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

        lem_inv_current_proposer_duty_is_rcvd_duty_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc'
        );
    }

    lemma lem_inv_current_proposer_duty_is_rcvd_duty_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_current_proposer_duty_is_rcvd_duty_body(process)
    ensures inv_current_proposer_duty_is_rcvd_duty_body(process')
    {
        var process_rcvd_duty := 
            process.(all_rcvd_duties := process.all_rcvd_duties + {proposer_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_proposer_duty(process_rcvd_duty);
        lem_inv_current_proposer_duty_is_rcvd_duty_f_terminate_current_proposer_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_current_proposer_duty_is_rcvd_duty_f_broadcast_randao_share(
            process_after_stopping_active_consensus_instance,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_current_proposer_duty_is_rcvd_duty_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_current_proposer_duty_is_rcvd_duty_body(process)
    ensures inv_current_proposer_duty_is_rcvd_duty_body(process')
    { }  

    lemma lem_inv_current_proposer_duty_is_rcvd_duty_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_current_proposer_duty_is_rcvd_duty_body(process)
    ensures inv_current_proposer_duty_is_rcvd_duty_body(process')
    { }

    lemma lem_inv_current_proposer_duty_is_rcvd_duty_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_current_proposer_duty_is_rcvd_duty_body(process)
    ensures inv_current_proposer_duty_is_rcvd_duty_body(process')
    { }  

    lemma lem_inv_current_proposer_duty_is_rcvd_duty_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_current_proposer_duty_is_rcvd_duty_body(process)
    ensures inv_current_proposer_duty_is_rcvd_duty_body(process')
    { }  

    lemma lem_inv_current_proposer_duty_is_rcvd_duty_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_current_proposer_duty_is_rcvd_duty_body(process)
    ensures inv_current_proposer_duty_is_rcvd_duty_body(process')
    { }  

    lemma lem_inv_latest_served_duty_is_rcvd_duty_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    { }

    lemma lem_inv_latest_served_duty_is_rcvd_duty_body_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    { } 

    lemma lem_inv_latest_served_duty_is_rcvd_duty_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state    
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
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
            lem_inv_latest_served_duty_is_rcvd_duty_body_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }  

    lemma lem_inv_latest_served_duty_is_rcvd_duty_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires proposer_duty in process.all_rcvd_duties
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    { }

    lemma lem_inv_latest_served_duty_is_rcvd_duty_body_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires proposer_duty in dvc.all_rcvd_duties
    requires inv_latest_served_duty_is_rcvd_duty_body(dvc)
    ensures inv_latest_served_duty_is_rcvd_duty_body(dvc')
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

        lem_inv_latest_served_duty_is_rcvd_duty_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc'
        );
    }

    lemma lem_inv_latest_served_duty_is_rcvd_duty_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    {
        var process_rcvd_duty := 
            process.(all_rcvd_duties := process.all_rcvd_duties + {proposer_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_proposer_duty(process_rcvd_duty);
        lem_inv_latest_served_duty_is_rcvd_duty_body_f_terminate_current_proposer_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_latest_served_duty_is_rcvd_duty_body_f_broadcast_randao_share(
            process_after_stopping_active_consensus_instance,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_latest_served_duty_is_rcvd_duty_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    { }  

    lemma lem_inv_latest_served_duty_is_rcvd_duty_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    { }

    lemma lem_inv_latest_served_duty_is_rcvd_duty_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    { }  

    lemma lem_inv_latest_served_duty_is_rcvd_duty_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    { }  

    lemma lem_inv_latest_served_duty_is_rcvd_duty_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_latest_served_duty_is_rcvd_duty_body(process)
    ensures inv_latest_served_duty_is_rcvd_duty_body(process')
    { }  

    lemma lem_inv_none_latest_served_duty_implies_none_current_proposer_duty_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_none_latest_served_duty_implies_none_current_proposer_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_proposer_duty_body(process')
    { }

    lemma lem_inv_none_latest_served_duty_implies_none_current_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_none_latest_served_duty_implies_none_current_proposer_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_proposer_duty_body(process')
    { }      

    lemma lem_inv_none_latest_served_duty_implies_none_current_proposer_duty_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state    
    requires inv_none_latest_served_duty_implies_none_current_proposer_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_proposer_duty_body(process')
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
            lem_inv_none_latest_served_duty_implies_none_current_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }   

    lemma lem_inv_none_latest_served_duty_implies_none_current_proposer_duty_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires proposer_duty in process.all_rcvd_duties
    requires inv_none_latest_served_duty_implies_none_current_proposer_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_proposer_duty_body(process')
    { }

    lemma lem_inv_none_latest_served_duty_implies_none_current_proposer_duty_body_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires proposer_duty in dvc.all_rcvd_duties
    requires inv_none_latest_served_duty_implies_none_current_proposer_duty_body(dvc)
    ensures inv_none_latest_served_duty_implies_none_current_proposer_duty_body(dvc')
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

        lem_inv_none_latest_served_duty_implies_none_current_proposer_duty_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc'
        );
    }

    lemma lem_inv_none_latest_served_duty_implies_none_current_proposer_duty_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_none_latest_served_duty_implies_none_current_proposer_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_proposer_duty_body(process')
    {
        var process_rcvd_duty := 
            process.(all_rcvd_duties := process.all_rcvd_duties + {proposer_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_proposer_duty(process_rcvd_duty);
        lem_inv_none_latest_served_duty_implies_none_current_proposer_duty_body_f_terminate_current_proposer_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_none_latest_served_duty_implies_none_current_proposer_duty_body_f_broadcast_randao_share(
            process_after_stopping_active_consensus_instance,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_none_latest_served_duty_implies_none_current_proposer_duty_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_none_latest_served_duty_implies_none_current_proposer_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_proposer_duty_body(process')
    { }

    lemma lem_inv_none_latest_served_duty_implies_none_current_proposer_duty_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_none_latest_served_duty_implies_none_current_proposer_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_proposer_duty_body(process')
    { }

    lemma lem_inv_none_latest_served_duty_implies_none_current_proposer_duty_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_none_latest_served_duty_implies_none_current_proposer_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_proposer_duty_body(process')
    { }  

    lemma lem_inv_none_latest_served_duty_implies_none_current_proposer_duty_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_none_latest_served_duty_implies_none_current_proposer_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_proposer_duty_body(process')
    { }  

    lemma lem_inv_none_latest_served_duty_implies_none_current_proposer_duty_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_none_latest_served_duty_implies_none_current_proposer_duty_body(process)
    ensures inv_none_latest_served_duty_implies_none_current_proposer_duty_body(process')
    { }  

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_served_duty_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(process')
    { }

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_served_duty_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(process')
    { }  

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_served_duty_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state    
    requires inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(process')
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
            lem_inv_current_proposer_duty_is_either_none_or_latest_served_duty_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }  

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_served_duty_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires proposer_duty in process.all_rcvd_duties
    requires inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(process')
    { }

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_served_duty_body_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires proposer_duty in dvc.all_rcvd_duties
    requires inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(dvc)
    ensures inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(dvc')
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

        lem_inv_current_proposer_duty_is_either_none_or_latest_served_duty_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc'
        );
    }

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_served_duty_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(process')
    {
        var process_rcvd_duty := 
            process.(all_rcvd_duties := process.all_rcvd_duties + {proposer_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_proposer_duty(process_rcvd_duty);
        lem_inv_current_proposer_duty_is_either_none_or_latest_served_duty_body_f_terminate_current_proposer_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_current_proposer_duty_is_either_none_or_latest_served_duty_body_f_broadcast_randao_share(
            process_after_stopping_active_consensus_instance,
            proposer_duty,
            process'
        );   
    }

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_served_duty_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(process')
    { }  

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_served_duty_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(process')
    { }

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_served_duty_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(process')
    { }  

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_served_duty_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(process')
    { }  

    lemma lem_inv_current_proposer_duty_is_either_none_or_latest_served_duty_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(process)
    ensures inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(process')
    { }  
    
    lemma lem_inv_available_current_proposer_duty_is_latest_served_proposer_duty_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process)
    ensures inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process')
    { }    

    lemma lem_inv_available_current_proposer_duty_is_latest_served_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process)
    ensures inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process')
    { }    

    lemma lem_inv_available_current_proposer_duty_is_latest_served_proposer_duty_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state    
    requires inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process)
    ensures inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process')
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
            lem_inv_available_current_proposer_duty_is_latest_served_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    } 

    lemma lem_inv_available_current_proposer_duty_is_latest_served_proposer_duty_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires proposer_duty in process.all_rcvd_duties
    requires inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process)
    ensures inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process')
    { }

    lemma lem_inv_available_current_proposer_duty_is_latest_served_proposer_duty_body_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires proposer_duty in dvc.all_rcvd_duties
    requires inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(dvc)
    ensures inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(dvc')
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

        lem_inv_available_current_proposer_duty_is_latest_served_proposer_duty_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc'
        );
    }

    lemma lem_inv_available_current_proposer_duty_is_latest_served_proposer_duty_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process)
    ensures inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process')
    {
        var process_rcvd_duty := 
            process.(all_rcvd_duties := process.all_rcvd_duties + {proposer_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_proposer_duty(process_rcvd_duty);
        lem_inv_available_current_proposer_duty_is_latest_served_proposer_duty_body_f_terminate_current_proposer_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_available_current_proposer_duty_is_latest_served_proposer_duty_body_f_broadcast_randao_share(
            process_after_stopping_active_consensus_instance,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_available_current_proposer_duty_is_latest_served_proposer_duty_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process)
    ensures inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process')
    { }  

    lemma lem_inv_available_current_proposer_duty_is_latest_served_proposer_duty_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process)
    ensures inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process')
    { }

    lemma lem_inv_available_current_proposer_duty_is_latest_served_proposer_duty_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process)
    ensures inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process')
    { }  

    lemma lem_inv_available_current_proposer_duty_is_latest_served_proposer_duty_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process)
    ensures inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process')
    { }  

    lemma lem_inv_available_current_proposer_duty_is_latest_served_proposer_duty_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process)
    ensures inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process')
    { }  

    lemma lem_inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process', 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served)
    { }

    lemma lem_inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process', 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served)
    { }
    
    lemma lem_inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state    
    requires inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
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
            lem_inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_start_consensus_if_can_construct_randao_share(
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

    lemma lem_inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires pred_proposer_duty_is_from_dv_seq_of_proposer_duties_new_body(  
                        proposer_duty,
                        hn,
                        sequence_proposer_duties_to_be_served, 
                        index_next_proposer_duty_to_be_served
                    )
    requires inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process', 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served)
    { }

    lemma lem_inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires pred_proposer_duty_is_from_dv_seq_of_proposer_duties_new_body(  
                        proposer_duty,
                        hn,
                        sequence_proposer_duties_to_be_served, 
                        index_next_proposer_duty_to_be_served
                    )
    requires inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    dvc, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
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

        lem_inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc',
            hn,
            sequence_proposer_duties_to_be_served,
            index_next_proposer_duty_to_be_served
        );
    }

    lemma lem_inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires pred_proposer_duty_is_from_dv_seq_of_proposer_duties_new_body(  
                        proposer_duty,
                        hn,
                        sequence_proposer_duties_to_be_served, 
                        index_next_proposer_duty_to_be_served
                    )
    requires inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process', 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served)
    {
        var process_rcvd_duty := 
            process.(all_rcvd_duties := process.all_rcvd_duties + {proposer_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_proposer_duty(process_rcvd_duty);
        lem_inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_terminate_current_proposer_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance,
            hn,
            sequence_proposer_duties_to_be_served,
            index_next_proposer_duty_to_be_served
        );
        lem_inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_broadcast_randao_share(
            process_after_stopping_active_consensus_instance,
            proposer_duty,
            process',
            hn,
            sequence_proposer_duties_to_be_served,
            index_next_proposer_duty_to_be_served
        );   
    }      

    lemma lem_inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_block_consensus_decided(
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
    requires inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process', 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served)
    { }  

    lemma lem_inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process', 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served)
    { }

    lemma lem_inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process', 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served)
    { }  

    lemma lem_inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process', 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served)
    { }  

    lemma lem_inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
             )
    ensures inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(
                    hn, 
                    process', 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served)
    { }    
    
    lemma lem_inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process')
    { }

    lemma lem_inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process)
    requires inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process')
    { }      

    lemma lem_inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state    
    requires inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(process)
    requires inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process')
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
            lem_inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires proposer_duty in process.all_rcvd_duties
    requires inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process')
    { }

    lemma lem_inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires proposer_duty in dvc.all_rcvd_duties
    requires inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(dvc)
    ensures inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(dvc')
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

        lem_inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc'
        );
    }

    lemma lem_inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process')
    {
        var process_rcvd_duty := 
            process.(all_rcvd_duties := process.all_rcvd_duties + {proposer_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_proposer_duty(process_rcvd_duty);
        lem_inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body_f_terminate_current_proposer_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body_f_broadcast_randao_share(
            process_after_stopping_active_consensus_instance,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process')
    { }  

    lemma lem_inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process')
    { }

    lemma lem_inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process')
    { }  

    lemma lem_inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process')
    { }  

    lemma lem_inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process)
    ensures inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process')
    { }      

    // lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_terminate_current_proposer_duty(
    //     process: DVCState,
    //     process': DVCState
    // )
    // requires f_terminate_current_proposer_duty.requires(process)
    // requires process' == f_terminate_current_proposer_duty(process)
    // requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process)
    // ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process')
    // { }

    // lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
    //     process: DVCState, 
    //     process': DVCState)
    // requires f_start_consensus_if_can_construct_randao_share.requires(process)
    // requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    // requires inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process)
    // requires inv_latest_served_duty_is_rcvd_duty_body(process)
    // requires inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_block_duties_body(process)
    // requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process)
    // ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process')
    // {

    // }      

    // lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_listen_for_randao_shares(
    //     process: DVCState, 
    //     randao_share: RandaoShare,
    //     process': DVCState)
    // requires f_listen_for_randao_shares.requires(process, randao_share)
    // requires process' == f_listen_for_randao_shares(process, randao_share).state    
    // requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process)
    // ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process')
    // { 
    //     var slot := randao_share.slot;
    //     var active_consensus_instances_on_beacon_blocks := process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys;

    //     if is_slot_for_current_or_future_instances(process, slot) 
    //     {
    //         var process_with_new_randao_share := 
    //             process.(
    //                 rcvd_randao_shares := process.rcvd_randao_shares[slot := getOrDefault(process.rcvd_randao_shares, slot, {}) + 
    //                                                                                 {randao_share} ]
    //             );   
    //         lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
    //             process_with_new_randao_share,
    //             process'
    //         );
    //     }
    //     else
    //     { }
    // }      

    // lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_check_for_next_duty(
    //     process: DVCState,
    //     proposer_duty: ProposerDuty,
    //     process': DVCState
    // )
    // requires f_check_for_next_duty.requires(process, proposer_duty)
    // requires process' == f_check_for_next_duty(process, proposer_duty).state
    // requires proposer_duty in process.all_rcvd_duties
    // requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process)
    // ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process')
    // { }

    // lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_broadcast_randao_share(
    //     dvc: DVCState,
    //     proposer_duty: ProposerDuty, 
    //     dvc': DVCState
    // )
    // requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    // requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    // requires proposer_duty in dvc.all_rcvd_duties
    // requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(dvc)
    // ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(dvc')
    // { 
    //     var slot := proposer_duty.slot;
    //     var fork_version := bn_get_fork_version(slot);    
    //     var epoch := compute_epoch_at_slot(slot);
    //     var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
    //     var randao_reveal_signature_share := rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, dvc.rs);
    //     var randao_share := 
    //         RandaoShare(
    //             proposer_duty := proposer_duty,
    //             slot := slot,
    //             signing_root := randao_reveal_signing_root,
    //             signature := randao_reveal_signature_share
    //         );
    //     var process_after_adding_randao_share :=
    //         dvc.(
    //                 randao_shares_to_broadcast := dvc.randao_shares_to_broadcast[proposer_duty.slot := randao_share]
    //         );

    //     lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_check_for_next_duty(
    //         process_after_adding_randao_share,
    //         proposer_duty,
    //         dvc'
    //     );
    // }

    // lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_serve_proposer_duty(
    //     process: DVCState,
    //     proposer_duty: ProposerDuty,
    //     process': DVCState
    // )  
    // requires f_serve_proposer_duty.requires(process, proposer_duty)
    // requires process' == f_serve_proposer_duty(process, proposer_duty).state
    // requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process)
    // ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process')
    // {
    //     var process_rcvd_duty := 
    //         process.(all_rcvd_duties := process.all_rcvd_duties + {proposer_duty});
    //     var process_after_stopping_active_consensus_instance := f_terminate_current_proposer_duty(process_rcvd_duty);
    //     lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_terminate_current_proposer_duty(
    //         process_rcvd_duty,
    //         process_after_stopping_active_consensus_instance
    //     );
    //     lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_broadcast_randao_share(
    //         process_after_stopping_active_consensus_instance,
    //         proposer_duty,
    //         process'
    //     );   
    // } 

    // lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_block_consensus_decided(
    //     process: DVCState,
    //     id: Slot,
    //     block: BeaconBlock, 
    //     process': DVCState
    // )
    // requires f_block_consensus_decided.requires(process, id, block)
    // requires process' == f_block_consensus_decided(process, id, block).state 
    // requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process)
    // ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process')
    // { }  

    // lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_listen_for_block_signature_shares(
    //     process: DVCState,
    //     block_share: SignedBeaconBlock,
    //     process': DVCState
    // )
    // requires f_listen_for_block_signature_shares.requires(process, block_share)
    // requires process' == f_listen_for_block_signature_shares(process, block_share).state
    // requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process)
    // ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process')
    // { }

    // lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_listen_for_new_imported_blocks(
    //     process: DVCState,
    //     block: BeaconBlock,
    //     process': DVCState
    // )
    // requires f_listen_for_new_imported_blocks.requires(process, block)
    // requires process' == f_listen_for_new_imported_blocks(process, block).state
    // requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process)
    // ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process')
    // { }  

    // lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_resend_randao_share(
    //     process: DVCState, 
    //     process': DVCState)
    // requires f_resend_randao_share.requires(process)
    // requires process' == f_resend_randao_share(process).state    
    // requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process)
    // ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process')
    // { }  

    // lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_resend_block_share(
    //     process: DVCState, 
    //     process': DVCState)
    // requires f_resend_block_share.requires(process)
    // requires process' == f_resend_block_share(process).state    
    // requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process)
    // ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process')
    // { }  

    // lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_add_block_to_bn(
    //     s: DVCState,
    //     block: BeaconBlock,
    //     s': DVCState 
    // )
    // requires f_add_block_to_bn.requires(s, block)
    // requires s' == f_add_block_to_bn(s, block)    
    // requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(s)
    // ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(s')
    // { }

    // lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_listen_for_block_signature_shares(
    //     process: DVCState,
    //     block_share: SignedBeaconBlock,
    //     process': DVCState
    // )
    // requires f_listen_for_block_signature_shares.requires(process, block_share)
    // requires process' == f_listen_for_block_signature_shares(process, block_share).state        
    // requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process)
    // ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process')
    // { }

    // lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_resend_block_share(
    //     process: DVCState,
    //     process': DVCState)
    // requires f_resend_block_share.requires(process)
    // requires process' == f_resend_block_share(process).state        
    // requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process)
    // ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process')
    // { } 

    // lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_terminate_current_proposer_duty(
    //     process: DVCState,
    //     process': DVCState
    // )
    // requires f_terminate_current_proposer_duty.requires(process)
    // requires process' == f_terminate_current_proposer_duty(process)
    // requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process)
    // ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process')
    // { }
    
    // lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
    //     process: DVCState, 
    //     proposer_duty: ProposerDuty, 
    //     process': DVCState)
    // requires f_start_consensus_if_can_construct_randao_share.requires(process, proposer_duty)
    // requires process' == f_start_consensus_if_can_construct_randao_share(process, proposer_duty).state   
    // requires inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process)
    // requires inv_latest_served_duty_is_rcvd_duty_body(process)
    // requires inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_block_duties_body(process, proposer_duty)
    // requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process)
    // ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process')
    // { } 

    // lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_check_for_next_duty(
    //     process: DVCState,
    //     proposer_duty: ProposerDuty,
    //     process': DVCState
    // )
    // requires f_check_for_next_duty.requires(process, proposer_duty)
    // requires process' == f_check_for_next_duty(process, proposer_duty).state        
    // requires inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process)
    // requires inv_latest_served_duty_is_rcvd_duty_body(process)
    // requires inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_block_duties_body(process, proposer_duty)
    // requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process)
    // ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process')
    // { }

    

    // lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_serve_proposer_duty(
    //     process: DVCState,
    //     proposer_duty: ProposerDuty,
    //     process': DVCState
    // )  
    // requires f_serve_proposer_duty.requires(process, proposer_duty)
    // requires process' == f_serve_proposer_duty(process, proposer_duty).state
    // requires inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process)   
    // requires inv_latest_served_duty_is_rcvd_duty_body(process)
    // requires inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_block_duties_body(process, proposer_duty)
    // requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process)
    // ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process')
    // { } 

    // lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_listen_for_new_imported_blocks(
    //     process: DVCState,
    //     block: BeaconBlock,
    //     process': DVCState
    // )
    // requires f_listen_for_new_imported_blocks.requires(process, block)
    // requires process' == f_listen_for_new_imported_blocks(process, block).state        
    // requires inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process)
    // requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process)
    // ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process')
    // { } 

    // lemma lem_inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body_f_block_consensus_decided(
    //     process: DVCState,
    //     id: Slot,
    //     block: BeaconBlock, 
    //     process': DVCState
    // )
    // requires f_block_consensus_decided.requires(process, id, block)
    // requires process' == f_block_consensus_decided(process, id, block).state         
    // requires inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(process)
    // requires inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process)
    // ensures inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(process')
    // { } 

    // lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_add_block_to_bn(
    //     s: DVCState,
    //     block: BeaconBlock,
    //     s': DVCState 
    // )
    // requires f_add_block_to_bn.requires(s, block)
    // requires s' == f_add_block_to_bn(s, block)    
    // requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(s)
    // ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(s')
    // { }

    // lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_listen_for_block_signature_shares(
    //     process: DVCState,
    //     block_share: SignedBeaconBlock,
    //     process': DVCState
    // )
    // requires f_listen_for_block_signature_shares.requires(process, block_share)
    // requires process' == f_listen_for_block_signature_shares(process, block_share).state        
    // requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process)
    // ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process')
    // { }

    // lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
    //     process: DVCState, 
    //     proposer_duty: ProposerDuty, 
    //     process': DVCState
    // )
    // requires f_start_consensus_if_can_construct_randao_share.requires(process, proposer_duty)
    // requires process' == f_start_consensus_if_can_construct_randao_share(process, proposer_duty).state   
    // requires proposer_duty in process.all_rcvd_duties
    // requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process)
    // ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process')
    // { } 

    // lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_f_resend_block_share(
    //     process: DVCState,
    //     process': DVCState)
    // requires f_resend_block_share.requires(process)
    // requires process' == f_resend_block_share(process).state        
    // requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process)
    // ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process')
    // { } 

    // lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_check_for_next_duty(
    //     process: DVCState,
    //     proposer_duty: ProposerDuty,
    //     process': DVCState
    // )
    // requires f_check_for_next_duty.requires(process, proposer_duty)
    // requires process' == f_check_for_next_duty(process, proposer_duty).state    
    // requires proposer_duty in process.all_rcvd_duties
    // requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process)
    // ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process')
    // { }

    // lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_block_consensus_decided(
    //     process: DVCState,
    //     id: Slot,
    //     block: BeaconBlock, 
    //     process': DVCState
    // )
    // requires f_block_consensus_decided.requires(process, id, block)
    // requires process' == f_block_consensus_decided(process, id, block).state         
    // requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process)
    // ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process')
    // { }

    // lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_terminate_current_proposer_duty(
    //     process: DVCState,
    //     process': DVCState
    // )
    // requires f_terminate_current_proposer_duty.requires(process)
    // requires process' == f_terminate_current_proposer_duty(process)
    // requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process)
    // ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process')
    // { }

    // lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_serve_proposer_duty(
    //     process: DVCState,
    //     proposer_duty: ProposerDuty,
    //     process': DVCState
    // )  
    // requires f_serve_proposer_duty.requires(process, proposer_duty)
    // requires process' == f_serve_proposer_duty(process, proposer_duty).state
    // requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process)
    // ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process')
    // {
    //     var process_rcvd_duty := 
    //             process.(all_rcvd_duties := process.all_rcvd_duties + {proposer_duty});
    //     var process_after_stopping_active_consensus_instance := f_terminate_current_proposer_duty(process_rcvd_duty);
    //     lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_terminate_current_proposer_duty(
    //         process_rcvd_duty,
    //         process_after_stopping_active_consensus_instance
    //     );
    //     lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_check_for_next_duty(
    //         process_after_stopping_active_consensus_instance,
    //         proposer_duty,
    //         process'
    //     );       
    // }

    // lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_listen_for_new_imported_blocks(
    //     process: DVCState,
    //     block: BeaconBlock,
    //     process': DVCState
    // )
    // requires f_listen_for_new_imported_blocks.requires(process, block)
    // requires process' == f_listen_for_new_imported_blocks(process, block).state        
    // requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process)
    // ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process')
    // { } 

    // lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_add_block_to_bn(
    //     s: DVCState,
    //     block: BeaconBlock,
    //     s': DVCState 
    // )
    // requires f_add_block_to_bn.requires(s, block)
    // requires s' == f_add_block_to_bn(s, block)    
    // requires inv_consensus_instances_only_for_rcvd_duties_body(s)
    // ensures inv_consensus_instances_only_for_rcvd_duties_body(s')
    // { }

    // lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_listen_for_block_signature_shares(
    //     process: DVCState,
    //     block_share: SignedBeaconBlock,
    //     process': DVCState
    // )
    // requires f_listen_for_block_signature_shares.requires(process, block_share)
    // requires process' == f_listen_for_block_signature_shares(process, block_share).state        
    // requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    // ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    // { }

    // lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_start_consensus_if_can_construct_randao_share(process: DVCState, proposer_duty: ProposerDuty, process': DVCState)
    // requires f_start_consensus_if_can_construct_randao_share.requires(process, proposer_duty)
    // requires process' == f_start_consensus_if_can_construct_randao_share(process, proposer_duty).state   
    // requires proposer_duty in process.all_rcvd_duties
    // requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    // ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    // { } 

    // lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_resend_block_share(
    //     process: DVCState,
    //     process': DVCState)
    // requires f_resend_block_share.requires(process)
    // requires process' == f_resend_block_share(process).state        
    // requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    // ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    // { } 

    // lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_check_for_next_duty(
    //     process: DVCState,
    //     proposer_duty: ProposerDuty,
    //     process': DVCState
    // )
    // requires f_check_for_next_duty.requires(process, proposer_duty)
    // requires process' == f_check_for_next_duty(process, proposer_duty).state    
    // requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    // requires proposer_duty in process.all_rcvd_duties
    // ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    // { }

    // lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_block_consensus_decided(
    //     process: DVCState,
    //     id: Slot,
    //     block: BeaconBlock, 
    //     process': DVCState
    // )
    // requires f_block_consensus_decided.requires(process, id, block)
    // requires process' == f_block_consensus_decided(process, id, block).state         
    // requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    // ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    // { }

    // lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_serve_proposer_duty(
    //     process: DVCState,
    //     proposer_duty: ProposerDuty,
    //     process': DVCState
    // )  
    // requires f_serve_proposer_duty.requires(process, proposer_duty)
    // requires process' == f_serve_proposer_duty(process, proposer_duty).state
    // requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    // ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    // { }

    // lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_listen_for_new_imported_blocks(
    //     process: DVCState,
    //     block: BeaconBlock,
    //     process': DVCState
    // )
    // requires f_listen_for_new_imported_blocks.requires(process, block)
    // requires process' == f_listen_for_new_imported_blocks(process, block).state        
    // requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    // ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    // { } 

    
}