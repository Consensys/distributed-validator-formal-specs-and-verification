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

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process')
    { }

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_current_proposer_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process')
    { }      

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_current_proposer_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process')
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
            lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires proposer_duty in process.all_rcvd_duties
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process')
    { }

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires proposer_duty in dvc.all_rcvd_duties
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(dvc)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(dvc')
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

        lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc'
        );
    }

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process')
    {
        var process_rcvd_duty := 
            process.(all_rcvd_duties := process.all_rcvd_duties + {proposer_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_proposer_duty(process_rcvd_duty);
        lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_terminate_current_proposer_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_broadcast_randao_share(
            process_after_stopping_active_consensus_instance,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process')
    { }  

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process')
    { }

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process')
    { }  

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process')
    { }  

    lemma lem_inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process)
    ensures inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(process')
    { }  

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    { }

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_current_proposer_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    { }      

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_current_proposer_duty_is_rcvd_duty_body(process)
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
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
            lem_inv_consensus_instances_only_for_rcvd_duties_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires proposer_duty in process.all_rcvd_duties
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    { }

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_broadcast_randao_share(
        dvc: DVCState,
        proposer_duty: ProposerDuty, 
        dvc': DVCState
    )
    requires f_broadcast_randao_share.requires(dvc, proposer_duty)
    requires dvc' == f_broadcast_randao_share(dvc, proposer_duty).state
    requires proposer_duty in dvc.all_rcvd_duties
    requires inv_consensus_instances_only_for_rcvd_duties_body(dvc)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(dvc')
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

        lem_inv_consensus_instances_only_for_rcvd_duties_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            dvc'
        );
    }

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    {
        var process_rcvd_duty := 
            process.(all_rcvd_duties := process.all_rcvd_duties + {proposer_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_proposer_duty(process_rcvd_duty);
        lem_inv_consensus_instances_only_for_rcvd_duties_body_f_terminate_current_proposer_duty(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_consensus_instances_only_for_rcvd_duties_body_f_broadcast_randao_share(
            process_after_stopping_active_consensus_instance,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    { }  

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    { }

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    { }  

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
    { }  

    lemma lem_inv_consensus_instances_only_for_rcvd_duties_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_consensus_instances_only_for_rcvd_duties_body(process)
    ensures inv_consensus_instances_only_for_rcvd_duties_body(process')
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
        var process_rcvd_duty := 
            process.(all_rcvd_duties := process.all_rcvd_duties + {proposer_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_proposer_duty(process_rcvd_duty);
        lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_terminate_current_proposer_duty(
            dv,
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );
        lem_inv_rcvd_block_shares_are_in_all_sent_messages_body_f_broadcast_randao_share(
            dv,
            process_after_stopping_active_consensus_instance,
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

    lemma lem_inv_the_latest_proposer_duty_was_sent_from_dv_body_f_terminate_current_proposer_duty(
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
    { 
        var process_rcvd_duty := 
            s.(all_rcvd_duties := s.all_rcvd_duties + {proposer_duty});
        var process_after_stopping_active_consensus_instance := f_terminate_current_proposer_duty(process_rcvd_duty);

        lem_f_terminate_current_proposer_duty_unchanged_vars(
            process_rcvd_duty,
            process_after_stopping_active_consensus_instance
        );

        lem_f_broadcast_randao_share_unchanged_vars(
            process_after_stopping_active_consensus_instance,
            proposer_duty,
            s'
        );   
    }

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

    // lemma lem_inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_ex_f_listen_for_block_signature_shares(
    //     process: DVCState,
    //     block_share: SignedBeaconBlock,
    //     s': DVCState,
    //     dv: DVState
    // )
    // requires f_listen_for_block_signature_shares.requires(process, block_share)
    // requires s' == f_listen_for_block_signature_shares(process, block_share).state
    // requires construct_complete_signed_block_assumptions_helper(
    //             process.construct_complete_signed_block,
    //             process.dv_pubkey,
    //             dv.all_nodes
    //         )
    // requires inv_quorum_constraints(dv)
    // requires block_share in dv.block_share_network.allMessagesSent
    // requires inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, process)
    // // ensures forall block | block in f_listen_for_block_signature_shares(process, block_share).outputs.submitted_blocks 
    // //                     ::  
    // //                     exists hn', block_share: SignedBeaconBlock 
    // //                         ::  
    // //                         inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(dv, hn', block_share, block);
    // {
    //     var slot := block_share.block.slot;

    //     if is_slot_for_current_or_future_instances(process, slot)
    //     {
    //          var data := block_share.block;
    //         var rcvd_block_shares_db_at_slot := getOrDefault(process.rcvd_block_shares, slot, map[]);
    //         var process_with_new_block_share :=
    //             process.(
    //                 rcvd_block_shares := 
    //                     process.rcvd_block_shares[
    //                         slot := 
    //                             rcvd_block_shares_db_at_slot[
    //                                 data := 
    //                                     getOrDefault(rcvd_block_shares_db_at_slot, data, {}) + 
    //                                     {block_share}
    //                                 ]
    //                     ]
    //             );            
                        
    //         if process.construct_complete_signed_block(process_with_new_block_share.rcvd_block_shares[slot][data]).isPresent() 
    //         {
    //             var block_shares := process_with_new_block_share.rcvd_block_shares[slot][data];
    //             var complete_signed_block := process.construct_complete_signed_block(block_shares).safe_get();                      
    //             var signing_root := compute_block_signing_root(complete_signed_block.block);
                
    //             assert construct_complete_signed_block_assumptions_reverse(
    //                         process.construct_complete_signed_block,
    //                         process.dv_pubkey,
    //                         dv.all_nodes
    //                     );

    //             assert signed_beacon_block_signer_threshold(dv.all_nodes, block_shares, signing_root);

                

    //             // var signers :=  
    //             //     set signer, block_share | 
    //             //         && block_share in block_shares
    //             //         && signer in dv.all_nodes
    //             //         && verify_bls_signature(signing_root, block_share.signature, signer)
    //             //     ::
    //             //         signer;

    //             // assert signers <= dv.all_nodes;

    //             // assert signed_beacon_block_signer_threshold(dv.all_nodes, block_shares, signing_root);

    //             // lemmaThereExistsAnHonestInQuorum(dv.all_nodes, dv.all_nodes - dv.honest_nodes_states.Keys, signers);

    //         //     var h_s :| h_s in dv.honest_nodes_states.Keys && h_s in signers;
    //         //     var h_s_att :| h_s_att in block_shares && verify_bls_signature(signing_root, h_s_att.signature, h_s);
        
    //         //     assert inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(
    //         //                     dv,
    //         //                     h_s,
    //         //                     h_s_att,
    //         //                     aggregated_proposer
    //         //                 );

    //         //     assert f_listen_for_block_signature_shares(process, block_share).outputs.submitted_blocks == {aggregated_proposer};

    //         //     assert forall a | a in f_listen_for_block_signature_shares(process, block_share).outputs.submitted_blocks ::
    //         //                 exists hn', block_share: SignedBeaconBlock :: inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(dv, hn', block_share, a);
    //         }
    //     }   
    // } 


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