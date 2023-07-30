include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_block_proposer.dfy"
include "../inv.dfy"
include "../../common/common_proofs.dfy"
include "../../../bn_axioms.dfy"
include "../../../rs_axioms.dfy"

include "../../../../common/commons.dfy"

include "../../common/dvc_block_proposer_instrumented.dfy"
include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../inv.dfy"



include "invs_fnc_1.dfy"



module Fnc_Invs_2
{
    import opened Types 
    import opened Common_Functions
    import opened Set_Seq_Helper
    import opened Signing_Methods
    import opened Consensus
    import opened Network_Spec
    import opened Block_DV
    import opened DV_Block_Proposer_Assumptions
    import opened Block_DVC
    import opened Consensus_Engine
    import opened Block_Inv_With_Empty_Initial_Block_Slashing_DB
    import opened Common_Proofs_For_Block_Proposer
    import opened BN_Axioms
    import opened RS_Axioms
    
    import opened Fnc_Invs_1
    
    lemma lem_inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_ces_f_check_for_next_duty_known_decision(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        block: BeaconBlock
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process)
    requires proposer_duty.slot in process.future_consensus_instances_on_blocks_already_decided.Keys
    requires block == process.future_consensus_instances_on_blocks_already_decided[proposer_duty.slot]
    ensures && var new_block_slashing_db := 
                    f_update_block_slashing_db(
                        process.block_slashing_db, 
                        block
                    );
            && inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_ces(
                            process.block_consensus_engine_state, 
                            new_block_slashing_db)
    {
        var slot := proposer_duty.slot;
        var block := process.future_consensus_instances_on_blocks_already_decided[slot];                
        var new_block_slashing_db := 
            f_update_block_slashing_db(process.block_slashing_db, block);      
            
        var slashing_db_block := construct_SlashingDBBlock_from_beacon_block(block);        
        assert new_block_slashing_db == process.block_slashing_db + {slashing_db_block};
        assert process.block_slashing_db <= new_block_slashing_db;
        assert inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_ces(
                            process.block_consensus_engine_state, 
                            process.block_slashing_db); 

        forall s: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> |
                            ( && s  in process.block_consensus_engine_state.slashing_db_hist.Keys
                            && vp in process.block_consensus_engine_state.slashing_db_hist[s]
                            && db in process.block_consensus_engine_state.slashing_db_hist[s][vp]
                            )   
        ensures db <= new_block_slashing_db               
        {
            calc {
                db; 
                <=
                process.block_slashing_db;
                <=
                new_block_slashing_db;
            }                        
        }

        assert inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_ces(
                        process.block_consensus_engine_state, 
                        new_block_slashing_db);
    }

    lemma lem_inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_f_add_block_to_bn(
        s: BlockDVCState,
        block: BeaconBlock,
        s': BlockDVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    requires inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(s)
    ensures inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(s')
    { }

    lemma lem_inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_f_start_consensus_if_can_construct_randao_share(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process)
    ensures inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process')
    { }      

    lemma lem_inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process)
    ensures inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process')
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_consensus_instance_indexed_k_is_for_rcvd_duty_at_slot_k_body(process)
    requires inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process)
    ensures inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process')
    { 
        var slot := proposer_duty.slot;
        if slot in process.future_consensus_instances_on_blocks_already_decided 
        {
            var block := process.future_consensus_instances_on_blocks_already_decided[slot];                
            var new_block_slashing_db := 
                f_update_block_slashing_db(process.block_slashing_db, block);            
            assert  inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_ces(
                            process.block_consensus_engine_state, 
                            process.block_slashing_db); 

            var slashing_db_block := construct_SlashingDBBlock_from_beacon_block(block);
            
            lem_inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_ces_f_check_for_next_duty_known_decision(
                process,
                proposer_duty,
                block
            );
        }
        else
        {
            lem_inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_f_start_consensus_if_can_construct_randao_share(
                process, 
                process'
            );
        }
    }

    lemma lem_inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    requires inv_consensus_instance_indexed_k_is_for_rcvd_duty_at_slot_k_body(process)
    requires inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process)
    ensures inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process')
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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

        lem_inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_consensus_instance_indexed_k_is_for_rcvd_duty_at_slot_k_body(process)
    requires inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process)
    ensures inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process')
    {
        var process_rcvd_duty := 
            f_receive_new_duty(process, proposer_duty);
       
        lem_inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_f_broadcast_randao_share(
            process_rcvd_duty,
            proposer_duty,
            process'
        );    
    } 

    lemma lem_inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        block: BeaconBlock, 
        process': BlockDVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process)
    ensures inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process')
    { 
        if && process.current_proposer_duty.isPresent()
           && process.current_proposer_duty.safe_get().slot == block.slot
           && id == block.slot
        {
            var new_block_slashing_db := f_update_block_slashing_db(process.block_slashing_db, block);
            
            assert  process.block_slashing_db
                    <=
                    process'.block_slashing_db
                    ;
            
            forall s: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock>  |
                ( && s in process'.block_consensus_engine_state.slashing_db_hist.Keys
                  && vp in process'.block_consensus_engine_state.slashing_db_hist[s].Keys
                  && db in process'.block_consensus_engine_state.slashing_db_hist[s][vp]
                )
            ensures db <= process'.block_slashing_db
            {
                if  && s in process.block_consensus_engine_state.slashing_db_hist.Keys
                    && vp in process.block_consensus_engine_state.slashing_db_hist[s].Keys
                    && db in process.block_consensus_engine_state.slashing_db_hist[s][vp]
                {   
                    assert  db <= process.block_slashing_db;
                    assert  db <= process'.block_slashing_db;                    
                }
                else
                {
                    assert  db == new_block_slashing_db;
                    assert  process'.block_slashing_db == new_block_slashing_db;
                    assert  db <= process'.block_slashing_db;
                }

            }            
        }
        else
        { }  
    }  

    lemma lem_inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process)
    ensures inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process')
    { }

    lemma lem_inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_consensus_instance_indexed_k_is_for_rcvd_duty_at_slot_k_body(process)
    requires inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process)
    ensures inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process')
    { 
        var new_consensus_instances_on_blocks_already_decided: map<Slot, BeaconBlock> := 
            map[ block.slot := block ];

        var consensus_instances_on_blocks_already_decided := process.future_consensus_instances_on_blocks_already_decided + new_consensus_instances_on_blocks_already_decided;

        var future_consensus_instances_on_blocks_already_decided := 
            f_listen_for_new_imported_blocks_helper(process, consensus_instances_on_blocks_already_decided);

        var process_after_stopping_consensus_instance :=
            process.(
                future_consensus_instances_on_blocks_already_decided := future_consensus_instances_on_blocks_already_decided,
                block_consensus_engine_state := f_stop_block_consensus_instances(
                                process.block_consensus_engine_state,
                                consensus_instances_on_blocks_already_decided.Keys
                ),
                block_shares_to_broadcast := process.block_shares_to_broadcast - consensus_instances_on_blocks_already_decided.Keys,
                rcvd_block_shares := process.rcvd_block_shares - consensus_instances_on_blocks_already_decided.Keys                    
            );   

        if && process_after_stopping_consensus_instance.current_proposer_duty.isPresent() 
            && process_after_stopping_consensus_instance.current_proposer_duty.safe_get().slot in consensus_instances_on_blocks_already_decided 
        {
            var decided_beacon_blocks := consensus_instances_on_blocks_already_decided[process.current_proposer_duty.safe_get().slot];
            var new_block_slashing_db := f_update_block_slashing_db(process.block_slashing_db, decided_beacon_blocks);             

            assert process'.block_slashing_db <= new_block_slashing_db;
            assert inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_ces(process_after_stopping_consensus_instance.block_consensus_engine_state, 
                              process.block_slashing_db); 

            forall s: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> |
                            ( && s  in process_after_stopping_consensus_instance.block_consensus_engine_state.slashing_db_hist.Keys
                              && vp in process_after_stopping_consensus_instance.block_consensus_engine_state.slashing_db_hist[s]
                              && db in process_after_stopping_consensus_instance.block_consensus_engine_state.slashing_db_hist[s][vp]
                            )   
            ensures db <= new_block_slashing_db               
            {
                calc {
                    db; 
                    <=
                    process_after_stopping_consensus_instance.block_slashing_db;
                    <=
                    new_block_slashing_db;
                }                        
            }
        }
        else
        {               
            assert inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process);
        }
    }  

    lemma lem_inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    requires inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process)
    ensures inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process')
    { }  

    lemma lem_inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body_f_resend_block_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state    
    requires inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process)
    ensures inv_every_db_in_slashing_db_hist_is_subset_of_block_slashing_db_body(process')
    { }  
    
    lemma lem_f_multicast_f_get_messages_from_messages_with_recipients(process: BlockDVCState, block_with_signature_share: SignedBeaconBlock)
    requires |process.peers| > 0    
    ensures f_get_messages_from_messages_with_recipients(f_multicast(block_with_signature_share, process.peers))
            ==
            { block_with_signature_share }            
    {
        var mcast_msgs := f_multicast(block_with_signature_share, process.peers);
        assert (forall msg | msg in mcast_msgs :: msg.message == block_with_signature_share);
        assert |mcast_msgs| > 0;
        
        var msgs_content := f_get_messages_from_messages_with_recipients(mcast_msgs);
        

        var all_mcast_msgs := mcast_msgs;
        var checked_mcast_msgs := {};

        while all_mcast_msgs != {}            
            invariant all_mcast_msgs + checked_mcast_msgs == mcast_msgs
            invariant   checked_mcast_msgs == {}
                        ==> 
                        f_get_messages_from_messages_with_recipients(checked_mcast_msgs) == {}
            invariant   checked_mcast_msgs != {}
                        ==> 
                        f_get_messages_from_messages_with_recipients(checked_mcast_msgs) == { block_with_signature_share } 
            decreases |all_mcast_msgs|
        {
            var msg :|  msg in all_mcast_msgs;
            assert msg.message ==  block_with_signature_share;
            all_mcast_msgs := all_mcast_msgs - {msg};
            checked_mcast_msgs := checked_mcast_msgs + {msg};
        }        

        assert f_get_messages_from_messages_with_recipients(mcast_msgs) == { block_with_signature_share };
    }

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_add_block_to_bn(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    ensures process'.block_shares_to_broadcast == process.block_shares_to_broadcast
    ensures process'.peers == process.peers         
    { }

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_start_consensus_if_can_construct_randao_share(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    ensures process'.block_shares_to_broadcast == process.block_shares_to_broadcast
    ensures process'.peers == process.peers       
    { }      

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    ensures process'.block_shares_to_broadcast == process.block_shares_to_broadcast
    ensures process'.peers == process.peers       
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }     

     lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    ensures process'.block_shares_to_broadcast == process.block_shares_to_broadcast
    ensures process'.peers == process.peers     
    { }

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    ensures process'.block_shares_to_broadcast == process.block_shares_to_broadcast
    ensures process'.peers == process.peers
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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

        lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    ensures process'.block_shares_to_broadcast == process.block_shares_to_broadcast
    ensures process'.peers == process.peers
    {
        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);

        lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    ensures process'.block_shares_to_broadcast == process.block_shares_to_broadcast
    ensures process'.peers == process.peers
    { }

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    ensures process'.block_shares_to_broadcast.Values <= process.block_shares_to_broadcast.Values
    ensures process'.peers == process.peers
    { }  

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    ensures process'.block_shares_to_broadcast == process.block_shares_to_broadcast
    ensures process'.peers == process.peers
    { }  

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_resend_block_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state    
    ensures process'.block_shares_to_broadcast == process.block_shares_to_broadcast
    ensures process'.peers == process.peers
    { }  

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock, 
        process': BlockDVCState,
        outputs: BlockOutputs
    )
    requires |process.peers| > 0
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state         
    requires outputs == f_block_consensus_decided(process, id, decided_beacon_block).outputs    
    requires decided_beacon_block.slot == id  
    ensures (process'.block_shares_to_broadcast.Values - process.block_shares_to_broadcast.Values) <= f_get_messages_from_messages_with_recipients(outputs.sent_block_shares);
    {   
        if  && process.current_proposer_duty.isPresent()
            && process.current_proposer_duty.safe_get().slot == decided_beacon_block.slot
            && id == decided_beacon_block.slot
        {
           var new_block_slashing_db := f_update_block_slashing_db(process.block_slashing_db, decided_beacon_block);
            var block_signing_root := compute_block_signing_root(decided_beacon_block);
            var fork_version := af_bn_get_fork_version(decided_beacon_block.slot);
            var block_signature := af_rs_sign_block(decided_beacon_block, fork_version, block_signing_root, process.rs);
            var block_share := SignedBeaconBlock(decided_beacon_block, block_signature);
            var slot := decided_beacon_block.slot;

            lem_f_multicast_f_get_messages_from_messages_with_recipients(process', block_share);
        }
        else
        {
        }
    }

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_add_block_to_bn(
        s: BlockDVCState,
        block: BeaconBlock,
        s': BlockDVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    ensures s'.rcvd_block_shares == s.rcvd_block_shares 
    { }

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_start_consensus_if_can_construct_randao_share(process: BlockDVCState, process': BlockDVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state       
    ensures process'.rcvd_block_shares == process.rcvd_block_shares
    { } 

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    ensures process'.rcvd_block_shares == process.rcvd_block_shares
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    } 

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state        
    ensures process'.rcvd_block_shares == process.rcvd_block_shares
    { }

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    ensures process'.rcvd_block_shares == process.rcvd_block_shares
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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

        lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    ensures process'.rcvd_block_shares == process.rcvd_block_shares
    {
        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);

        lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        block: BeaconBlock, 
        process': BlockDVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    ensures process'.rcvd_block_shares == process.rcvd_block_shares
    { }  

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state         
    ensures && var slot := block_share.block.slot;
            && var data := block_share.block;
            && ( forall i, j 
                    | 
                        && i in process'.rcvd_block_shares.Keys
                        && j in process'.rcvd_block_shares[i].Keys
                    :: 
                        && ( (  || i != slot
                                || j != data
                             )
                             ==> 
                             process'.rcvd_block_shares[i][j] == process.rcvd_block_shares[i][j]
                           )
                        && ( ( && i == slot
                               && j == data
                             )
                             ==> 
                                &&  var rcvd_block_shares_db_at_slot := get_or_default(process.rcvd_block_shares, slot, map[]);

                                &&  process'.rcvd_block_shares[i][j] 
                                    <= 
                                     get_or_default(rcvd_block_shares_db_at_slot, data, {}) + {block_share} 
                           )
                   )                                      
    { }

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state   
    ensures process'.rcvd_block_shares.Keys <= process.rcvd_block_shares.Keys
    ensures ( forall i, j 
                    | 
                        && i in process'.rcvd_block_shares 
                        && j in process'.rcvd_block_shares[i]
                    :: 
                        (
                        && i in process.rcvd_block_shares 
                        && j in process.rcvd_block_shares[i]
                        && ( process'.rcvd_block_shares[i][j] 
                             <= 
                             process.rcvd_block_shares[i][j] 
                           )
                        )
            )  
    { } 
    
    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    ensures process'.rcvd_block_shares == process.rcvd_block_shares
    { }  

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_resend_block_shares(
        process: BlockDVCState,
        process': BlockDVCState)
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state        
    ensures process'.rcvd_block_shares == process.rcvd_block_shares
    { } 

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_listen_for_block_signature_shares_domain(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state         
    ensures && var slot := block_share.block.slot;
            && var data := block_share.block;
            && ( forall i, j 
                    | 
                        || i != slot
                        || j != data                 
                    :: 
                        ( && i in process'.rcvd_block_shares.Keys
                          && j in process'.rcvd_block_shares[i].Keys               
                        )
                        ==>
                        ( && i in process.rcvd_block_shares.Keys
                          && j in process.rcvd_block_shares[i].Keys               
                        )
            )
    { 
        var activate_block_consensus_intances := process.block_consensus_engine_state.active_consensus_instances.Keys;
        var slot := block_share.block.slot;

        if  is_slot_for_current_or_future_instances(process, slot) 
        {
            var block_shares_db_at_slot := get_or_default(process.rcvd_block_shares, block_share.block.slot, map[]);
            var slot := block_share.block.slot;
            var data := block_share.block;
            assert && ( block_share.block.slot in process.rcvd_block_shares.Keys
                        ==> 
                        block_shares_db_at_slot == process.rcvd_block_shares[block_share.block.slot]
                      )
                   && ( block_share.block.slot !in process.rcvd_block_shares.Keys
                        ==> 
                        block_shares_db_at_slot == map[]
                      );

            var new_set := get_or_default(block_shares_db_at_slot, data, {}) + {block_share};
            assert && ( data in block_shares_db_at_slot.Keys 
                        ==> 
                        new_set == block_shares_db_at_slot[data] + {block_share}
                      )
                   && ( data !in block_shares_db_at_slot.Keys 
                        ==> 
                        new_set == {block_share}
                      );
                
            var new_block_shares_db := 
                        process.rcvd_block_shares[
                            block_share.block.slot := 
                                block_shares_db_at_slot[
                                            data := new_set                                                
                                            ]
                                ];
            assert block_share.block.slot in new_block_shares_db.Keys;
            assert data in new_block_shares_db[block_share.block.slot].Keys;
            assert ( forall i, j 
                    | 
                        || i != slot
                        || j != data                    
                    :: 
                        ( && i in new_block_shares_db.Keys
                          && j in new_block_shares_db[i].Keys               
                        )
                        ==>
                        ( && i in process.rcvd_block_shares.Keys
                          && j in process.rcvd_block_shares[i].Keys               
                        )
                    )
            ;

            var process_mod := process.(
                    rcvd_block_shares := new_block_shares_db
                );
            assert ( forall i, j 
                    | 
                        || i != slot
                        || j != data
                    :: 
                        ( && i in process_mod.rcvd_block_shares.Keys
                          && j in process_mod.rcvd_block_shares[i].Keys               
                        )
                        ==>
                        ( && i in process.rcvd_block_shares.Keys
                          && j in process.rcvd_block_shares[i].Keys               
                        )
                    )
            ;         
        }
        else
        {             
            assert process'.rcvd_block_shares == process.rcvd_block_shares;            
        }
    }  


    lemma lem_inv_block_slashing_db_is_monotonic_body_f_add_block_to_bn(
        s: BlockDVCState,
        block: BeaconBlock,
        s': BlockDVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    ensures inv_block_slashing_db_is_monotonic_body(s, s') 
    { }

    lemma lem_inv_block_slashing_db_is_monotonic_body_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state        
    ensures inv_block_slashing_db_is_monotonic_body(process, process')
    { }

    lemma lem_inv_block_slashing_db_is_monotonic_body_f_start_consensus_if_can_construct_randao_share(process: BlockDVCState, process': BlockDVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state       
    ensures inv_block_slashing_db_is_monotonic_body(process, process')
    { } 

    lemma lem_inv_block_slashing_db_is_monotonic_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    ensures inv_block_slashing_db_is_monotonic_body(process, process')
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_block_slashing_db_is_monotonic_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    } 

    lemma lem_inv_block_slashing_db_is_monotonic_body_f_resend_block_shares(
        process: BlockDVCState,
        process': BlockDVCState)
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state        
    ensures inv_block_slashing_db_is_monotonic_body(process, process')    
    { } 

    lemma lem_inv_block_slashing_db_is_monotonic_body_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state        
    ensures inv_block_slashing_db_is_monotonic_body(process, process')
    { }

    lemma lem_inv_block_slashing_db_is_monotonic_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    ensures inv_block_slashing_db_is_monotonic_body(process, process')
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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

        lem_inv_block_slashing_db_is_monotonic_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_block_slashing_db_is_monotonic_body_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock, 
        process': BlockDVCState
    )
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state         
    ensures inv_block_slashing_db_is_monotonic_body(process, process')
    { }

    lemma lem_inv_block_slashing_db_is_monotonic_body_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    ensures inv_block_slashing_db_is_monotonic_body(process, process')
    {
        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);

        lem_inv_block_slashing_db_is_monotonic_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );        
    }

    lemma lem_inv_block_slashing_db_is_monotonic_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    ensures inv_block_slashing_db_is_monotonic_body(process, process')
    { }

    lemma lem_inv_block_slashing_db_is_monotonic_body_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state   
    ensures inv_block_slashing_db_is_monotonic_body(process, process')
    { } 

    lemma lem_inv_block_slashing_db_is_monotonic_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    ensures inv_block_slashing_db_is_monotonic_body(process, process')
    { }  

    

    lemma lem_inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body_f_add_block_to_bn(
        s: BlockDVCState,
        block: BeaconBlock,
        s': BlockDVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(s)
    ensures inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(s')
    { }

    lemma lem_inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body_f_start_consensus_if_can_construct_randao_share(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)
    ensures inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process')
    { }      

    lemma lem_inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)
    ensures inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process')
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)
    ensures inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process')
    { }

    lemma lem_inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)
    ensures inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process')
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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

        lem_inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)
    ensures inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process')
    {
        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);
       
        lem_inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        block: BeaconBlock, 
        process': BlockDVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)
    ensures inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process')
    { }  

    lemma lem_inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)
    ensures inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process')
    { }

    lemma lem_inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)
    ensures inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process')
    { }  

    lemma lem_inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)
    ensures inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process')
    { }  

    lemma lem_inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body_f_resend_block_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state    
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)
    ensures inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process')
    { } 

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_add_block_to_bn(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
    { }

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_start_consensus_if_can_construct_randao_share(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
    { }      

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
    { }

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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

        lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
    {
        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);
       
        lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        block: BeaconBlock, 
        process': BlockDVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
    { }  

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
    { }

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
    { }  

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
    { }  

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_resend_block_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state    
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
    { }  

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body_f_add_block_to_bn(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState,
        hn: BLSPubkey,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                process, 
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                process',
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    { }

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body_f_start_consensus_if_can_construct_randao_share(
        process: BlockDVCState, 
        process': BlockDVCState,
        hn: BLSPubkey,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                process, 
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                process',
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)  
    { } 

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState,
        hn: BLSPubkey,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                process, 
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                process',
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)  
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process',
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served
            );
        }
        else
        { }
    }  

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState,
        hn: BLSPubkey,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                process, 
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                process',
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)  
    { } 

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState,
        hn: BLSPubkey,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                process, 
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                process',
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)  
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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

        lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process', 
            hn,
            sequence_of_proposer_duties_to_be_served, 
            index_next_proposer_duty_to_be_served
        );
    }

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState,
        hn: BLSPubkey,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body_helper( 
                proposer_duty,
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served
            )
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                process, 
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                process',
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)  
    { 
        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);

        forall duty: ProposerDuty | duty in process_after_receiving_duty.all_rcvd_duties
        ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body_helper(        
                    duty,
                    hn, 
                    sequence_of_proposer_duties_to_be_served,    
                    index_next_proposer_duty_to_be_served
                )
        {
            if duty in process.all_rcvd_duties
            {
                assert inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body_helper(        
                    duty,
                    hn, 
                    sequence_of_proposer_duties_to_be_served,    
                    index_next_proposer_duty_to_be_served
                );
            }
            else
            {
                assert duty == proposer_duty;
                assert inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body_helper(        
                    duty,
                    hn, 
                    sequence_of_proposer_duties_to_be_served,    
                    index_next_proposer_duty_to_be_served
                );
            }
        }

        assert  inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                    process_after_receiving_duty, 
                    hn, 
                    sequence_of_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
                );

        lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process', 
            hn, 
            sequence_of_proposer_duties_to_be_served, 
            index_next_proposer_duty_to_be_served
        );
    }

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock, 
        process': BlockDVCState,
        hn: BLSPubkey,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state 
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                process, 
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                process',
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)  
    { }  


    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState,
        hn: BLSPubkey,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                process, 
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                process',
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)  
    {}

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState,
        hn: BLSPubkey,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                process, 
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                process',
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)  
    { }   

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState,
        hn: BLSPubkey,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat  
    )
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                process, 
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                process',
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)  
    { } 

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body_f_resend_block_shares(
        s: BlockDVCState,
        s': BlockDVCState,
        hn: BLSPubkey,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat  
    )
    requires f_resend_block_shares.requires(s)
    requires s' == f_resend_block_shares(s).state
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                s, 
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_proposer_duties_body(
                s',
                hn, 
                sequence_of_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)  
    { } 

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_add_block_to_bn(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    { }

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_start_consensus_if_can_construct_randao_share(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    { }      

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires && process.latest_proposer_duty.isPresent()
             && process.all_rcvd_duties != {}
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    { }

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.all_rcvd_duties != {}
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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

        lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    {
        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);
       
        lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );
    } 

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        block: BeaconBlock, 
        process': BlockDVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    { }  

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    { }

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    { }  

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    { }  

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_resend_block_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state    
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    { }  

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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

        assert inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process_after_adding_randao_share);

        lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    requires inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_proposer_duties_body(process, proposer_duty)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
    { 
        assert inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process);

        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);

        assert inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process_after_receiving_duty);
       
        lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_add_block_to_bn(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
    { } 

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    } 

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        block: BeaconBlock, 
        process': BlockDVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_resend_block_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state    
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
    { } 

    lemma lem_inv_submitted_outputs_blocks_are_valid_f_start_consensus_if_can_construct_randao_share(
        process: BlockDVCState, 
        process': BlockDVCState
    )
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    ensures inv_submitted_outputs_blocks_are_valid(
                f_start_consensus_if_can_construct_randao_share(process).outputs,
                process'.dv_pubkey
                )
    { }  

    lemma lem_inv_submitted_outputs_blocks_are_valid_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState
    )
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    ensures inv_submitted_outputs_blocks_are_valid(
                f_listen_for_randao_shares(process, randao_share).outputs,
                process'.dv_pubkey
            )
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_submitted_outputs_blocks_are_valid_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }    

    lemma lem_inv_submitted_outputs_blocks_are_valid_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    ensures inv_submitted_outputs_blocks_are_valid(
                f_check_for_next_duty(process, proposer_duty).outputs,
                process'.dv_pubkey
            )
    { }

    lemma lem_inv_submitted_outputs_blocks_are_valid_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    ensures inv_submitted_outputs_blocks_are_valid(
                f_broadcast_randao_share(process, proposer_duty).outputs,
                process'.dv_pubkey
            )
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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

        lem_inv_submitted_outputs_blocks_are_valid_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_submitted_outputs_blocks_are_valid_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    ensures inv_submitted_outputs_blocks_are_valid(
                f_serve_proposer_duty(process, proposer_duty).outputs,
                process'.dv_pubkey
            )
    {
        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);

        lem_inv_submitted_outputs_blocks_are_valid_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_submitted_outputs_blocks_are_valid_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock, 
        process': BlockDVCState
    )
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state 
    ensures inv_submitted_outputs_blocks_are_valid(
                f_block_consensus_decided(process, id, decided_beacon_block).outputs,
                process'.dv_pubkey
            )
    { }  

    lemma lem_inv_submitted_outputs_blocks_are_valid_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires assump_construction_of_complete_signed_block_reverse(
                process.construct_complete_signed_block,
                process.dv_pubkey,
                process.peers
             )
    ensures inv_submitted_outputs_blocks_are_valid(
                f_listen_for_block_signature_shares(process, block_share).outputs,
                process'.dv_pubkey
            )
    { 
        var slot := block_share.block.slot;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var data := block_share.block;
            var rcvd_block_shares_db_at_slot := get_or_default(process.rcvd_block_shares, slot, map[]);
            var process_with_new_block_share :=
                process.(
                    rcvd_block_shares := 
                        process.rcvd_block_shares[
                            slot := 
                                rcvd_block_shares_db_at_slot[
                                    data := 
                                        get_or_default(rcvd_block_shares_db_at_slot, data, {}) + 
                                        {block_share}
                                    ]
                        ]
                );            
            if process.construct_complete_signed_block(process_with_new_block_share.rcvd_block_shares[slot][data]).isPresent() 
            {                
                    var complete_signed_block := process.construct_complete_signed_block(process_with_new_block_share.rcvd_block_shares[slot][data]).safe_get();                      

                    alem_rs_block_sign_and_verification_propeties();
                    assert  is_valid_signed_beacon_block(complete_signed_block, process_with_new_block_share.dv_pubkey);
                    assert  process.dv_pubkey
                            ==
                            process_with_new_block_share.dv_pubkey 
                            == 
                            process'.dv_pubkey
                            ;
                    assert  is_valid_signed_beacon_block(complete_signed_block, process'.dv_pubkey);
                    assert  inv_submitted_outputs_blocks_are_valid(
                                f_listen_for_block_signature_shares(process, block_share).outputs,
                                process'.dv_pubkey
                            );
            }
            else 
            { }
        }
        else
        { }
    }

    lemma lem_inv_submitted_outputs_blocks_are_valid_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    ensures inv_submitted_outputs_blocks_are_valid(
                f_listen_for_new_imported_blocks(process, block).outputs,
                process'.dv_pubkey
            )
    { }  

    lemma lem_inv_submitted_outputs_blocks_are_valid_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    ensures inv_submitted_outputs_blocks_are_valid(
                f_resend_randao_shares(process).outputs,
                process'.dv_pubkey
            )
    { }  

    lemma lem_inv_submitted_outputs_blocks_are_valid_f_resend_block_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state    
    ensures inv_submitted_outputs_blocks_are_valid(
                f_resend_block_shares(process).outputs,
                process'.dv_pubkey
            )
    { }  

    lemma lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_start_consensus_if_can_construct_randao_share(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    ensures && var outputs := f_start_consensus_if_can_construct_randao_share(process).outputs;
            && inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(outputs, process')
    { }  

    lemma lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    ensures && var outputs := f_listen_for_randao_shares(process, randao_share).outputs;
            && inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(outputs, process')
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    } 
        
    lemma lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    ensures && var outputs := f_resend_randao_shares(process).outputs;
            && inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(outputs, process')
    { }  

    lemma lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_resend_block_shares(
        process: BlockDVCState,
        process': BlockDVCState
    )
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state    
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures && var outputs := f_resend_block_shares(process).outputs;
            && inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(outputs, process')
    {
        var new_outputs := f_get_empty_block_ouputs().(
                                    sent_block_shares :=
                                        f_multicast_multiple(process.block_shares_to_broadcast.Values, process.peers)
                                );

    }  

    lemma lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    ensures && var outputs := f_check_for_next_duty(process, proposer_duty).outputs;
            && inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(outputs, process')
    { }

    lemma lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    ensures && var outputs := f_broadcast_randao_share(process, proposer_duty).outputs;
            && inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(outputs, process')
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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

        lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    ensures && var outputs := f_serve_proposer_duty(process, proposer_duty).outputs;
            && inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(outputs, process')
    {
        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);
        
        
        lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock, 
        process': BlockDVCState
    )
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state 
    ensures && var outputs := f_block_consensus_decided(process, id, decided_beacon_block).outputs;
            && inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(outputs, process')
    { 
        if  && process.current_proposer_duty.isPresent()
            && process.current_proposer_duty.safe_get().slot == decided_beacon_block.slot
            && id == decided_beacon_block.slot
        {
            var new_block_slashing_db := f_update_block_slashing_db(process.block_slashing_db, decided_beacon_block);
            var block_signing_root := compute_block_signing_root(decided_beacon_block);
            var fork_version := af_bn_get_fork_version(decided_beacon_block.slot);
            var block_signature := af_rs_sign_block(decided_beacon_block, fork_version, block_signing_root, process.rs);
            var block_share := SignedBeaconBlock(decided_beacon_block, block_signature);

            alem_rs_block_sign_and_verification_propeties( );
            assert  verify_bls_signature(
                        block_signing_root, 
                        block_share.signature, 
                        process.rs.pubkey
                    );

            var outputs := f_block_consensus_decided(process, id, decided_beacon_block).outputs;

            forall block_share: SignedBeaconBlock | block_share in f_get_messages_from_messages_with_recipients(outputs.sent_block_shares) 
            ensures inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_body(process', block_share);
            {                
                assert inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_body(process', block_share);
            }
        }     
        else 
        {
            var outputs := f_block_consensus_decided(process, id, decided_beacon_block).outputs;
            assert inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(outputs, process');
        }
    }  
    
    lemma lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    ensures && var outputs := f_listen_for_block_signature_shares(process, block_share).outputs;
            && inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(outputs, process')
    { }

    lemma lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    ensures && var outputs := f_listen_for_new_imported_blocks(process, block).outputs;
            && inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(outputs, process')
    { }  

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_add_block_to_bn(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
    { }

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_start_consensus_if_can_construct_randao_share(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
    { }      

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
    { }

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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

        lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
    {
        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);
       
        lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        ); 
    } 

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock, 
        process': BlockDVCState
    )
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state 
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
    { 
        if  && process.current_proposer_duty.isPresent()
            && process.current_proposer_duty.safe_get().slot == decided_beacon_block.slot
            && id == decided_beacon_block.slot
        {
           var new_block_slashing_db := f_update_block_slashing_db(process.block_slashing_db, decided_beacon_block);
            var new_slashingDB_block := construct_SlashingDBBlock_from_beacon_block(decided_beacon_block);      
            assert  new_block_slashing_db
                    == 
                    process.block_slashing_db + {new_slashingDB_block}  
                    ;              


            var block_signing_root := compute_block_signing_root(decided_beacon_block);
            var fork_version := af_bn_get_fork_version(decided_beacon_block.slot);
            var block_signature := af_rs_sign_block(decided_beacon_block, fork_version, block_signing_root, process.rs);
            var new_block_share := SignedBeaconBlock(decided_beacon_block, block_signature);

            alem_rs_block_sign_and_verification_propeties();           
            assert verify_bls_signature(block_signing_root, new_block_share.signature, process.rs.pubkey);
            assert pred_is_owner_of_block_share(process.rs.pubkey, new_block_share);            
        }     
        else 
        {
            var outputs := f_block_consensus_decided(process, id, decided_beacon_block).outputs;
            assert inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process');
        }
    } 

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
    { }

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
    { }  

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
    { }  

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_resend_block_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state    
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
    { }  

    lemma lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers_f_start_consensus_if_can_construct_randao_share(
        process: BlockDVCState, 
        process': BlockDVCState
    )
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    ensures inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers(                
                f_start_consensus_if_can_construct_randao_share(process).outputs,
                process'
            )
    { }  

    lemma lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    ensures inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers(
                f_check_for_next_duty(process, proposer_duty).outputs,
                process'
            )
    { }

    lemma lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    ensures inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers(
                f_broadcast_randao_share(process, proposer_duty).outputs,
                process'
            )
    { }

    lemma lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    ensures inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers(
                f_serve_proposer_duty(process, proposer_duty).outputs,
                process'
            )
    {
        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);


        lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers_f_listen_for_randao_shares(
        process: BlockDVCState,
        randao_share: RandaoShare,
        process': BlockDVCState
    )
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state
    ensures inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers(
                f_listen_for_randao_shares(process, randao_share).outputs,
                process'
            )
    { }  

    lemma lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    ensures inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers(
                f_listen_for_new_imported_blocks(process, block).outputs,
                process'
            )
    { }  

    lemma lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires assump_construction_of_complete_signed_block_reverse(
                process.construct_complete_signed_block,
                process.dv_pubkey,
                process.peers
             )
    ensures inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers(
                f_listen_for_block_signature_shares(process, block_share).outputs,
                process'
                )
    { 
        var slot := block_share.block.slot;

        if is_slot_for_current_or_future_instances(process, slot)
        {
            var data := block_share.block;
            var rcvd_block_shares_db_at_slot := get_or_default(process.rcvd_block_shares, slot, map[]);
            var process_with_new_block_share :=
                process.(
                    rcvd_block_shares := 
                        process.rcvd_block_shares[
                            slot := 
                                rcvd_block_shares_db_at_slot[
                                    data := 
                                        get_or_default(rcvd_block_shares_db_at_slot, data, {}) + 
                                        {block_share}
                                    ]
                        ]
                );    
                        
            if process.construct_complete_signed_block(process_with_new_block_share.rcvd_block_shares[slot][data]).isPresent() 
            {
                assert  inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers(
                            f_listen_for_block_signature_shares(process, block_share).outputs,
                            process'
                        );            
            }
            else 
            {
                assert  inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers(
                            f_listen_for_block_signature_shares(process, block_share).outputs,
                            process'
                        );
            }
        }            
        else 
        {
            assert  inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers(
                        f_listen_for_block_signature_shares(process, block_share).outputs,
                        process'
                    );
        }
            
    }

    lemma lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock, 
        process': BlockDVCState
    )
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state 
    ensures inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers(
                f_block_consensus_decided(process, id, decided_beacon_block).outputs,
                process'
            )
    { }  

    lemma lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    ensures inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers(
                f_resend_randao_shares(process).outputs,
                process'
            )
    { }  

    lemma lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers_f_resend_block_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state    
    ensures inv_outputs_blocks_submited_are_created_based_on_shares_from_quorum_of_rs_signers(
                f_resend_block_shares(process).outputs,
                process'
            )
    { } 

    lemma lem_inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_add_block_to_bn(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
    { }

    lemma lem_inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_start_consensus_if_can_construct_randao_share(        
        process: BlockDVCState, 
        process': BlockDVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state   
    requires (  forall block_share: SignedBeaconBlock |
                    && block_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_owner_of_block_share(rs_pubkey, block_share)
                    ::
                    && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process, block_share)             
            )
    requires inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
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
               && proposer_duty.slot !in process.block_consensus_engine_state.active_consensus_instances.Keys 
            {
                var rs_pubkey: BLSPubkey := process.rs.pubkey;
                assert rs_pubkey == process'.rs.pubkey;

                var duty_slot := proposer_duty.slot;
                var block_slashing_db := process.block_slashing_db;
                var block_slashing_db' := process'.block_slashing_db;
                assert block_slashing_db == block_slashing_db';
                assert  (  forall block_share: SignedBeaconBlock |
                            && block_share in allMessagesSent 
                            && pred_is_owner_of_block_share(rs_pubkey, block_share)
                            ::
                            && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process', block_share)             
                        );

                var slashing_db_hist: map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>> 
                    := process.block_consensus_engine_state.slashing_db_hist;        
                var slashing_db_hist': map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>> 
                    := process'.block_consensus_engine_state.slashing_db_hist;
                    
                var bcvc := 
                    BlockConsensusValidityCheckState(
                        proposer_duty := proposer_duty,
                        randao_reveal := constructed_randao_reveal.safe_get(),
                        validityPredicate := (bb: BeaconBlock) => ci_decision_is_valid_beacon_block(
                                                                        block_slashing_db, 
                                                                        bb, 
                                                                        proposer_duty,
                                                                        constructed_randao_reveal.safe_get()
                                                                    )
                    );
                var new_vp := bcvc.validityPredicate;
                var new_active_consensus_instances := 
                    process.block_consensus_engine_state.active_consensus_instances[
                        duty_slot := bcvc
                    ];              

                assert  slashing_db_hist' == 
                        f_update_block_slashing_db_hist_with_new_id_and_vp(
                            slashing_db_hist,
                            duty_slot,
                            bcvc.validityPredicate,
                            block_slashing_db                    
                        );

                forall slot: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> | 
                    && slot in slashing_db_hist'.Keys
                    && vp in slashing_db_hist'[slot].Keys
                    && db in slashing_db_hist'[slot][vp]
                ensures inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(            
                                allMessagesSent,
                                process'.rs.pubkey,
                                slot,
                                vp,
                                db
                            );   
                {
                    if slot != duty_slot || vp != new_vp
                    {
                        assert inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(            
                            allMessagesSent,
                            process.rs.pubkey,
                            slot,
                            vp,
                            db
                        );                
                    }
                    else
                    {
                        var hist_slot := get_or_default(slashing_db_hist, slot, map[]);
                        var hist_slot_vp := get_or_default(hist_slot, vp, {});
                        var new_hist_slot := get_or_default(slashing_db_hist', slot, map[]);
                        var new_hist_slot_vp := get_or_default(new_hist_slot, vp, {});

                        assert  slashing_db_hist' == 
                                f_update_block_slashing_db_hist_with_new_id_and_vp(
                                    slashing_db_hist,
                                    slot,
                                    bcvc.validityPredicate,
                                    block_slashing_db                    
                                );
                        
                        assert hist_slot_vp + {block_slashing_db} == new_hist_slot_vp;

                        if db in hist_slot_vp
                        {                    
                            assert  inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(            
                                        allMessagesSent,
                                        process'.rs.pubkey,
                                        slot,
                                        vp,
                                        db
                                    );   
                        }
                        else
                        {
                            assert db == block_slashing_db;
                            forall block_share: SignedBeaconBlock |
                                        && block_share in allMessagesSent 
                                        && pred_is_owner_of_block_share(rs_pubkey, block_share)
                            {
                                var block := block_share.block;
                                var slashing_db_block 
                                    := 
                                    construct_SlashingDBBlock_from_beacon_block(block);
                                assert inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process', block_share);
                                assert slashing_db_block in process'.block_slashing_db;     
                                assert slashing_db_block in db;                    
                            }
                        }
                    }
                }
            }
            else
            {
                assert  inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                            allMessagesSent,
                            process'
                        );
            }
        }
        else
        {
            assert  inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                            allMessagesSent,
                            process'
                    );
        }        
    }  

    lemma lem_inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires (  forall block_share: SignedBeaconBlock |
                    && block_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_owner_of_block_share(rs_pubkey, block_share)
                    ::
                    && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process, block_share)             
            )
    requires inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   

            var rs_pubkey: BLSPubkey := process.rs.pubkey;
            assert rs_pubkey == process_with_new_randao_share.rs.pubkey;

            lem_inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process',
                allMessagesSent
            );
        }
        else
        { }
    } 

    lemma lem_inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_update_block_slashing_db_hist_with_new_consensus_instances_and_slashing_db_blocks(
        hist: map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>>,
        new_active_consensus_instances : map<Slot, BlockConsensusValidityCheckState>,
        new_block_slashing_db: set<SlashingDBBlock>,
        new_hist: map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>>,
        allMessagesSent: set<SignedBeaconBlock>,
        rs_pubkey: BLSPubkey
    )    
    requires new_hist == f_update_block_slashing_db_hist_with_new_consensus_instances_and_slashing_db_blocks(hist, new_active_consensus_instances, new_block_slashing_db)
    requires (  forall slot: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> | 
                        && slot in hist
                        && vp in hist[slot]
                        && db in hist[slot][vp]
                        :: 
                        inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(
                            allMessagesSent,
                            rs_pubkey,
                            slot,
                            vp,
                            db
                        )
    )
    requires (  forall block_share: SignedBeaconBlock | 
                        && block_share in allMessagesSent 
                        && pred_is_owner_of_block_share(rs_pubkey, block_share)
                        ::
                        && var block := block_share.block;
                        && var slashing_db_block := construct_SlashingDBBlock_from_beacon_block(block);
                        && slashing_db_block in new_block_slashing_db           
    )
    ensures ( forall slot: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock>, block_share: SignedBeaconBlock | 
                    && slot in new_hist.Keys
                    && vp in new_hist[slot]
                    && db in new_hist[slot][vp]
                    && block_share in allMessagesSent
                    && pred_is_owner_of_block_share(rs_pubkey, block_share)
                    && block_share.block.slot < slot             
                    ::
                    inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(
                        allMessagesSent,
                        rs_pubkey,
                        slot,
                        vp,
                        db
                    )
    )
    {
        assert hist.Keys + new_active_consensus_instances.Keys == new_hist.Keys;

        forall slot: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock>, block_share: SignedBeaconBlock | 
                    && slot in new_hist.Keys
                    && vp in new_hist[slot]
                    && db in new_hist[slot][vp]
                    && block_share in allMessagesSent
                    && pred_is_owner_of_block_share(rs_pubkey, block_share)
                    && block_share.block.slot < slot             
        ensures inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(
                        allMessagesSent,
                        rs_pubkey,
                        slot,
                        vp,
                        db
                    )
        {
            if slot in new_active_consensus_instances.Keys
            {
                if slot in hist.Keys && vp in hist[slot].Keys && db in hist[slot][vp]
                {                    
                    assert inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(
                        allMessagesSent,
                        rs_pubkey,
                        slot,
                        vp,
                        db
                    );                
                }
                else
                {
                    assert db == new_block_slashing_db;
                    assert inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(
                        allMessagesSent,
                        rs_pubkey,
                        slot,
                        vp,
                        db
                    );      
                }
            }
            else
            {
                assert hist[slot] == new_hist[slot];
                assert inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(
                            allMessagesSent,
                            rs_pubkey,
                            slot,
                            vp,
                            db
                        );
            }
        }
    }

    

    lemma lem_inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_update_block_consensus_engine_state(
        s: ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>,
        new_block_slashing_db: set<SlashingDBBlock>,
        s': ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires s' == f_update_block_consensus_engine_state(s, new_block_slashing_db)
    {
        var new_active_consensus_instances := f_update_block_consensus_instance_validity_check_states(
                    s.active_consensus_instances,
                    new_block_slashing_db
                );

        forall slot: Slot | slot in new_active_consensus_instances.Keys
        ensures && var validityPredicate := new_active_consensus_instances[slot].validityPredicate;
                && var proposer_duty := new_active_consensus_instances[slot].proposer_duty;
                && var randao_reveal := new_active_consensus_instances[slot].randao_reveal;
                && ( forall block: BeaconBlock 
                        ::
                        validityPredicate(block)
                        <==> 
                        ci_decision_is_valid_beacon_block(new_block_slashing_db, block, proposer_duty, randao_reveal)
                )
        {
            var validityPredicate := new_active_consensus_instances[slot].validityPredicate;
            var proposer_duty := new_active_consensus_instances[slot].proposer_duty;
            var randao_reveal := new_active_consensus_instances[slot].randao_reveal;
            assert  ( forall block: BeaconBlock 
                        ::
                        validityPredicate(block)
                        <==> 
                        ci_decision_is_valid_beacon_block(new_block_slashing_db, block, proposer_duty, randao_reveal)
                    )
            ;
        }

        assert  s' 
                ==
                s.(
                    active_consensus_instances := new_active_consensus_instances,
                    slashing_db_hist := f_update_block_slashing_db_hist_with_new_consensus_instances_and_slashing_db_blocks(
                        s.slashing_db_hist,
                        new_active_consensus_instances,
                        new_block_slashing_db
                    )
                );
    }

    lemma lem_inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_check_for_next_duty(        
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires (  forall block_share: SignedBeaconBlock |
                    && block_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_owner_of_block_share(rs_pubkey, block_share)
                    ::
                    && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process, block_share)             
            )
    requires inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
    { 
        var slot := proposer_duty.slot;
        if  slot in process.future_consensus_instances_on_blocks_already_decided.Keys 
        {
            var block := process.future_consensus_instances_on_blocks_already_decided[slot];                
            var new_block_slashing_db := 
                f_update_block_slashing_db(
                    process.block_slashing_db, 
                    process.future_consensus_instances_on_blocks_already_decided[proposer_duty.slot]
                );
            assert process.block_slashing_db <= new_block_slashing_db;

            var new_active_consensus_instances := f_update_block_consensus_instance_validity_check_states(
                    process.block_consensus_engine_state.active_consensus_instances,
                    new_block_slashing_db
                );

            var new_process := 
                process.(
                    current_proposer_duty := None,                          
                    future_consensus_instances_on_blocks_already_decided := process.future_consensus_instances_on_blocks_already_decided - {proposer_duty.slot},
                    block_slashing_db := new_block_slashing_db,
                    block_consensus_engine_state := f_update_block_consensus_engine_state(
                        process.block_consensus_engine_state,
                        new_block_slashing_db
                    )                        
                );

            lem_inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_update_block_slashing_db_hist_with_new_consensus_instances_and_slashing_db_blocks(
                process.block_consensus_engine_state.slashing_db_hist,                 
                new_active_consensus_instances,
                new_block_slashing_db,
                process'.block_consensus_engine_state.slashing_db_hist,
                allMessagesSent,
                process.rs.pubkey
            );
        }
        else
        {
            lem_inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_start_consensus_if_can_construct_randao_share(                
                process, 
                process',
                allMessagesSent
            );
        }
    }  

    lemma lem_inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    requires (  forall block_share: SignedBeaconBlock |
                    && block_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_owner_of_block_share(rs_pubkey, block_share)
                    ::
                    && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process, block_share)             
            )
    requires inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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

        lem_inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process',
            allMessagesSent
        );
    }

    lemma lem_inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_serve_proposer_duty(        
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires (  forall block_share: SignedBeaconBlock |
                    && block_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_owner_of_block_share(rs_pubkey, block_share)
                    ::
                    && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process, block_share)             
            )
    requires inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
    {
        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);

        assert  inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                                    
                    allMessagesSent,
                    process_after_receiving_duty                    
                );

        assert  (  forall block_share: SignedBeaconBlock |
                                && block_share in allMessagesSent 
                                && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                                && pred_is_owner_of_block_share(rs_pubkey, block_share)
                                ::
                                && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process_after_receiving_duty, block_share)             
                );

        lem_inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process',
            allMessagesSent
        );  
    }   

    lemma lem_inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires (  forall block_share: SignedBeaconBlock |
                    && block_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_owner_of_block_share(rs_pubkey, block_share)
                    ::
                    && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process, block_share)             
            )
    requires inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
    { 
        var new_consensus_instances_on_blocks_already_decided: map<Slot, BeaconBlock> := 
            map[ block.slot := block ];

        var consensus_instances_on_blocks_already_decided := process.future_consensus_instances_on_blocks_already_decided + new_consensus_instances_on_blocks_already_decided;

        var future_consensus_instances_on_blocks_already_decided := 
            f_listen_for_new_imported_blocks_helper(process, consensus_instances_on_blocks_already_decided);

        var process_after_stopping_consensus_instance :=
                process.(
                    future_consensus_instances_on_blocks_already_decided := future_consensus_instances_on_blocks_already_decided,
                    block_consensus_engine_state := f_stop_block_consensus_instances(
                                    process.block_consensus_engine_state,
                                    consensus_instances_on_blocks_already_decided.Keys
                    ),
                    block_shares_to_broadcast := process.block_shares_to_broadcast - consensus_instances_on_blocks_already_decided.Keys,
                    rcvd_block_shares := process.rcvd_block_shares - consensus_instances_on_blocks_already_decided.Keys                    
                );         

        assert inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process_after_stopping_consensus_instance
            );          
        assert (  forall block_share: SignedBeaconBlock |
                    && block_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_owner_of_block_share(rs_pubkey, block_share)
                    ::
                    && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process_after_stopping_consensus_instance, block_share)             
            );

        if  && process_after_stopping_consensus_instance.current_proposer_duty.isPresent() 
            && process_after_stopping_consensus_instance.current_proposer_duty.safe_get().slot in consensus_instances_on_blocks_already_decided 
        {
            var decided_beacon_block := consensus_instances_on_blocks_already_decided[process_after_stopping_consensus_instance.current_proposer_duty.safe_get().slot];
            var new_block_slashing_db := f_update_block_slashing_db(process_after_stopping_consensus_instance.block_slashing_db, decided_beacon_block);
            
            assert process_after_stopping_consensus_instance.block_slashing_db <= new_block_slashing_db;

            var new_active_consensus_instances := f_update_block_consensus_instance_validity_check_states(
                    process_after_stopping_consensus_instance.block_consensus_engine_state.active_consensus_instances,
                    new_block_slashing_db
                );

            assert  process'.block_consensus_engine_state.slashing_db_hist 
                    == 
                    f_update_block_slashing_db_hist_with_new_consensus_instances_and_slashing_db_blocks(
                        process_after_stopping_consensus_instance.block_consensus_engine_state.slashing_db_hist, 
                        new_active_consensus_instances, 
                        new_block_slashing_db
                    );

            lem_inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_update_block_slashing_db_hist_with_new_consensus_instances_and_slashing_db_blocks(
                process_after_stopping_consensus_instance.block_consensus_engine_state.slashing_db_hist,                 
                new_active_consensus_instances,
                new_block_slashing_db,
                process'.block_consensus_engine_state.slashing_db_hist,
                allMessagesSent,
                process.rs.pubkey
            );
        }
        else
        {
            assert inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            );
        }
    }  

    lemma lem_inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_block_consensus_decided_new_sent_block_shares(        
        process: BlockDVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock, 
        process': BlockDVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state         
    requires (  forall block_share: SignedBeaconBlock |
                    && block_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_owner_of_block_share(rs_pubkey, block_share)
                    ::
                    && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process, block_share)             
            )
    requires inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    requires && process.current_proposer_duty.isPresent()
             && id == process.current_proposer_duty.safe_get().slot
             && id == decided_beacon_block.slot
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    requires ( forall slot  |
                        slot in process'.block_consensus_engine_state.slashing_db_hist.Keys
                        ::
                        slot <= process'.latest_proposer_duty.safe_get().slot
             )
    ensures && var outputs := f_block_consensus_decided(process, id, decided_beacon_block).outputs;
            && var allMessagesSent' := allMessagesSent + f_get_messages_from_messages_with_recipients(outputs.sent_block_shares);
            && inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                    allMessagesSent',
                    process'
                )
    ensures && var new_block_slashing_db := f_update_block_slashing_db(process.block_slashing_db, decided_beacon_block);
            && var block_signing_root := compute_block_signing_root(decided_beacon_block);
            && var fork_version := af_bn_get_fork_version(decided_beacon_block.slot);
            && var block_signature := af_rs_sign_block(decided_beacon_block, fork_version, block_signing_root, process.rs);
            && var block_share := SignedBeaconBlock(decided_beacon_block, block_signature); 
            && pred_is_owner_of_block_share(process'.rs.pubkey, block_share)
            && ( forall slot: Slot | slot in process'.block_consensus_engine_state.slashing_db_hist.Keys ::
                    block_share.block.slot >= slot
            )
    {
        var new_block_slashing_db := f_update_block_slashing_db(process.block_slashing_db, decided_beacon_block);
        var block_signing_root := compute_block_signing_root(decided_beacon_block);
        var fork_version := af_bn_get_fork_version(decided_beacon_block.slot);
        var block_signature := af_rs_sign_block(decided_beacon_block, fork_version, block_signing_root, process.rs);
        var block_share := SignedBeaconBlock(decided_beacon_block, block_signature);
        var slot := decided_beacon_block.slot;

        alem_rs_block_sign_and_verification_propeties();        
        assert verify_bls_signature(
                        block_signing_root,
                        af_rs_sign_block(decided_beacon_block, fork_version, block_signing_root, process.rs),
                        process.rs.pubkey
                    );
        assert pred_is_owner_of_block_share(process.rs.pubkey, block_share);
        assert process'.rs.pubkey == process.rs.pubkey;
        assert pred_is_owner_of_block_share(process'.rs.pubkey, block_share);

        assert process.block_slashing_db <= new_block_slashing_db;                                                    

        assert process.latest_proposer_duty.isPresent();
        assert && process'.latest_proposer_duty.isPresent()
               && process'.latest_proposer_duty.safe_get()
                  ==
                  process.latest_proposer_duty.safe_get()  ;

        var new_active_consensus_instances := f_update_block_consensus_instance_validity_check_states(
                process.block_consensus_engine_state.active_consensus_instances,
                new_block_slashing_db
            );        

        lem_inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_update_block_slashing_db_hist_with_new_consensus_instances_and_slashing_db_blocks(
            process.block_consensus_engine_state.slashing_db_hist,                 
            new_active_consensus_instances,
            new_block_slashing_db,
            process'.block_consensus_engine_state.slashing_db_hist,
            allMessagesSent,
            process.rs.pubkey
        );

        assert  inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(
                    allMessagesSent,
                    process'
                );
        assert process.rs.pubkey == process'.rs.pubkey;

        var allMessagesSent' := allMessagesSent + {block_share};

        forall slot: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> | 
                    && slot in process'.block_consensus_engine_state.slashing_db_hist.Keys
                    && vp in process'.block_consensus_engine_state.slashing_db_hist[slot].Keys
                    && db in process'.block_consensus_engine_state.slashing_db_hist[slot][vp]
        ensures inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(
                    allMessagesSent',
                    process'.rs.pubkey,
                    slot,
                    vp,
                    db
                )
        {
            var hist := process.block_consensus_engine_state.slashing_db_hist;
            var hist' := process'.block_consensus_engine_state.slashing_db_hist;            
            var hist_slot := get_or_default(hist, slot, map[]);
            var hist_slot' := get_or_default(hist', slot, map[]);
            var hist_slot_vp := get_or_default(hist_slot, vp, {});
            var hist_slot_vp' := get_or_default(hist_slot', vp, {});

            assert || hist_slot_vp' == hist_slot_vp 
                   || hist_slot_vp' == hist_slot_vp + {new_block_slashing_db};

            forall block_share: SignedBeaconBlock | 
                && block_share in allMessagesSent'
                && pred_is_owner_of_block_share(process'.rs.pubkey, block_share)
                && block_share.block.slot < slot
            ensures && var block := block_share.block;
                    && var slashing_db_block := construct_SlashingDBBlock_from_beacon_block(block);
                    && slashing_db_block in db
            {
                var block := block_share.block;
                var slashing_db_block := 
                    construct_SlashingDBBlock_from_beacon_block(block);

                if block_share in allMessagesSent
                {
                    assert slashing_db_block in db;
                }
                else
                {
                    
                    assert block_share == block_share;
                    assert block_share.block.slot >= slot;
                }
                assert slashing_db_block in db;
            }
        }
    }

    lemma lem_inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
             )    
    { }

    lemma lem_inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock, 
        process': BlockDVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state         
    requires (  forall block_share: SignedBeaconBlock |
                    && block_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_owner_of_block_share(rs_pubkey, block_share)
                    ::
                    && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process, block_share)             
            )
    requires inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
             )          
    { 
        if  && process.current_proposer_duty.isPresent()
            && process.current_proposer_duty.safe_get().slot == decided_beacon_block.slot
            && id == decided_beacon_block.slot
        {
            
        }
        else 
        {
            assert inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            );
        }
            
    }

    lemma lem_inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_resend_block_shares(        
        process: BlockDVCState,
        process': BlockDVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state       
    requires process.block_shares_to_broadcast.Values <= allMessagesSent 
    requires inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
    { }

    lemma lem_inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    requires inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
    { }  

    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_add_block_to_bn(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    ensures process.rs.pubkey == process'.rs.pubkey
    { }
    
    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_start_consensus_if_can_construct_randao_share(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    ensures process.rs.pubkey == process'.rs.pubkey
    { }   

    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    ensures process.rs.pubkey == process'.rs.pubkey
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_unchanged_dvc_rs_pubkey_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }        
    }  

    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    ensures process.rs.pubkey == process'.rs.pubkey
    { }

    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    ensures process.rs.pubkey == process'.rs.pubkey
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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

        lem_inv_unchanged_dvc_rs_pubkey_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    ensures process.rs.pubkey == process'.rs.pubkey
    {
        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);
       
        lem_inv_unchanged_dvc_rs_pubkey_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );
    } 

    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        block: BeaconBlock, 
        process': BlockDVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    ensures process.rs.pubkey == process'.rs.pubkey
    { }  

    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    ensures process.rs.pubkey == process'.rs.pubkey
    { }

    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    ensures process.rs.pubkey == process'.rs.pubkey
    { }  

    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    ensures process.rs.pubkey == process'.rs.pubkey
    { }  

    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_resend_block_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state    
    ensures process.rs.pubkey == process'.rs.pubkey
    { }     

    lemma lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_add_block_to_bn(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_of_proposer_duties_to_be_served, n, process, index_next_proposer_duty_to_be_served)
    ensures inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_of_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served)
    { }    

    lemma lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_start_block_consensus_instance_helper(
        s: ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>,
        id: Slot,
        proposer_duty: ProposerDuty,
        block_slashing_db: set<SlashingDBBlock>,
        complete_signed_randao_reveal: BLSSignature,
        s': ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>
    )
    requires f_start_block_consensus_instance.requires(s, id, proposer_duty, block_slashing_db, complete_signed_randao_reveal)
    requires s' == f_start_block_consensus_instance(s, id, proposer_duty, block_slashing_db, complete_signed_randao_reveal)
    ensures s.slashing_db_hist.Keys + { proposer_duty.slot } == s'.slashing_db_hist.Keys
    {  }


    lemma lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_start_consensus_if_can_construct_randao_share(
        process: BlockDVCState,        
        process': BlockDVCState,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state  
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)
    requires inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_of_proposer_duties_to_be_served, n, process, index_next_proposer_duty_to_be_served)
    requires inv_available_current_proposer_duty_is_from_dv_seq_of_proposer_duties_body(process, n, sequence_of_proposer_duties_to_be_served, index_next_proposer_duty_to_be_served)
    ensures inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_of_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served)
    {
        if && process.current_proposer_duty.isPresent()
           && process.current_proposer_duty.safe_get().slot in process.rcvd_randao_shares
        {
            var proposer_duty := process.current_proposer_duty.safe_get();
            assert  && process'.current_proposer_duty.isPresent()
                    && proposer_duty == process'.current_proposer_duty.safe_get();
            var all_rcvd_randao_sig := 
                    set randao_share | randao_share in process.rcvd_randao_shares[
                                                process.current_proposer_duty.safe_get().slot]
                                                    :: randao_share.signature;                
            var constructed_randao_reveal := process.construct_complete_signed_randao_reveal(all_rcvd_randao_sig);
            if && constructed_randao_reveal.isPresent()  
               && proposer_duty.slot !in process.block_consensus_engine_state.active_consensus_instances.Keys 
            {
                lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_start_block_consensus_instance_helper(
                    process.block_consensus_engine_state,
                    proposer_duty.slot,
                    proposer_duty,
                    process.block_slashing_db,
                    constructed_randao_reveal.safe_get(),
                    process'.block_consensus_engine_state
                );
            }
            else
            { }
        }
        else
        { }
    }

    lemma lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)
    requires inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_of_proposer_duties_to_be_served, n, process, index_next_proposer_duty_to_be_served)
    requires inv_available_current_proposer_duty_is_from_dv_seq_of_proposer_duties_body(process, n, sequence_of_proposer_duties_to_be_served, index_next_proposer_duty_to_be_served)
    ensures inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_of_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served)
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process',
                sequence_of_proposer_duties_to_be_served,
                n,
                index_next_proposer_duty_to_be_served
            );
        }
        else
        { }
    } 

    lemma lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_update_block_consensus_engine_state_helper(
        s: ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>,
        new_block_slashing_db: set<SlashingDBBlock>,
        s': ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>
    )
    requires f_update_block_consensus_engine_state.requires(s, new_block_slashing_db)
    requires s' == f_update_block_consensus_engine_state(s, new_block_slashing_db)
    ensures && var new_active_block_consensus_instances := 
                        f_update_block_consensus_instance_validity_check_states(
                            s.active_consensus_instances,
                            new_block_slashing_db
                        );
            && s.slashing_db_hist.Keys + new_active_block_consensus_instances.Keys == s'.slashing_db_hist.Keys
    { }

    lemma lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state  
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)
    requires inv_available_current_proposer_duty_is_from_dv_seq_of_proposer_duties_body(process, n, sequence_of_proposer_duties_to_be_served, index_next_proposer_duty_to_be_served)
    requires inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_of_proposer_duties_to_be_served, n, process, index_next_proposer_duty_to_be_served)
    requires pred_last_proposer_duty_is_delivering_to_given_honest_node(proposer_duty, sequence_of_proposer_duties_to_be_served, n, index_next_proposer_duty_to_be_served)
    ensures inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_of_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served)
    {   
        var slot := proposer_duty.slot;
        if  slot in process.future_consensus_instances_on_blocks_already_decided.Keys 
        {
            var new_block_slashing_db := 
                    f_update_block_slashing_db(
                        process.block_slashing_db, 
                        process.future_consensus_instances_on_blocks_already_decided[proposer_duty.slot]
                    );
            lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_update_block_consensus_engine_state_helper(
                    process.block_consensus_engine_state,
                    new_block_slashing_db,
                    process'.block_consensus_engine_state
            );
            assert inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_of_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served);
        }
        else
        {
            lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_start_consensus_if_can_construct_randao_share(
                process,
                process',
                sequence_of_proposer_duties_to_be_served,
                n,
                index_next_proposer_duty_to_be_served
            );
            assert inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_of_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served);
        }            
    }

    lemma lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)
    requires inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_of_proposer_duties_to_be_served, n, process, index_next_proposer_duty_to_be_served)
    requires pred_last_proposer_duty_is_delivering_to_given_honest_node(proposer_duty, sequence_of_proposer_duties_to_be_served, n, index_next_proposer_duty_to_be_served)
    requires inv_available_current_proposer_duty_is_from_dv_seq_of_proposer_duties_body(process, n, sequence_of_proposer_duties_to_be_served, index_next_proposer_duty_to_be_served)
    ensures inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_of_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served)
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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

        lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process',
            sequence_of_proposer_duties_to_be_served,
            n,
            index_next_proposer_duty_to_be_served
        );
    }

    lemma lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state  
    requires index_next_proposer_duty_to_be_served > 0    
    requires inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_of_proposer_duties_to_be_served, n, process, index_next_proposer_duty_to_be_served-1)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)
    requires pred_last_proposer_duty_is_delivering_to_given_honest_node(proposer_duty, sequence_of_proposer_duties_to_be_served, n, index_next_proposer_duty_to_be_served)
    ensures inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_of_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served)
    {
        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);
       
        lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process',
            sequence_of_proposer_duties_to_be_served,
            n,
            index_next_proposer_duty_to_be_served
        );
    }       

    lemma lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock,        
        process': BlockDVCState,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat        
    )
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state
    requires inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(
                sequence_of_proposer_duties_to_be_served, 
                n, 
                process, 
                index_next_proposer_duty_to_be_served
                )
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)
    ensures inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(
                sequence_of_proposer_duties_to_be_served, 
                n, 
                process', 
                index_next_proposer_duty_to_be_served
                )
    { }   

    lemma lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat        
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(
                sequence_of_proposer_duties_to_be_served, 
                n, 
                process, 
                index_next_proposer_duty_to_be_served
                )
    ensures inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(
                sequence_of_proposer_duties_to_be_served, 
                n, 
                process', 
                index_next_proposer_duty_to_be_served
            )
    { } 

    lemma lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_of_proposer_duties_to_be_served, n, process, index_next_proposer_duty_to_be_served)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)
    ensures inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_of_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served)
    { }   

    lemma lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat        
    )
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    requires inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_of_proposer_duties_to_be_served, n, process, index_next_proposer_duty_to_be_served)
    ensures inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_of_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served)
    { }  

    lemma lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body_f_resend_block_shares(
        process: BlockDVCState, 
        process': BlockDVCState,
        sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat        
    )
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state    
    requires inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_of_proposer_duties_to_be_served, n, process, index_next_proposer_duty_to_be_served)
    ensures inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(sequence_of_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served)
    { }       

    lemma lem_inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_helper(
        s: BlockDVState,
        event: DVBlockEvent,
        s': BlockDVState,
        s_node: BlockDVCState,
        n: BLSPubkey
    )
    requires next_event_preconditions(s, event)
    requires next_event(s, event, s')      
    requires inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(s.sequence_of_proposer_duties_to_be_served, n, s_node, s.index_next_proposer_duty_to_be_served)
    ensures inv_exists_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_slashing_db_hist_body(s'.sequence_of_proposer_duties_to_be_served, n, s_node, s.index_next_proposer_duty_to_be_served)
    { }  

    lemma lem_inv_unchanged_rs_f_add_block_to_bn(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    ensures inv_unchanged_rs_body(process, process')
    { }

    lemma lem_inv_unchanged_rs_f_start_consensus_if_can_construct_randao_share(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    ensures inv_unchanged_rs_body(process, process')
    { }      

    lemma lem_inv_unchanged_rs_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    ensures inv_unchanged_rs_body(process, process')
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_unchanged_rs_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    } 

    lemma lem_inv_unchanged_rs_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    ensures inv_unchanged_rs_body(process, process')
    { }

    lemma lem_inv_unchanged_rs_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    ensures inv_unchanged_rs_body(process, process')
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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

        lem_inv_unchanged_rs_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_unchanged_rs_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    ensures inv_unchanged_rs_body(process, process')
    {
        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);

        lem_inv_unchanged_rs_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_unchanged_rs_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        block: BeaconBlock, 
        process': BlockDVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    ensures inv_unchanged_rs_body(process, process')
    { }  

    lemma lem_inv_unchanged_rs_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    ensures inv_unchanged_rs_body(process, process')
    { }

    lemma lem_inv_unchanged_rs_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    ensures inv_unchanged_rs_body(process, process')
    { }  

    lemma lem_inv_unchanged_rs_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    ensures inv_unchanged_rs_body(process, process')
    { }  

    lemma lem_inv_unchanged_rs_f_resend_block_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state    
    ensures inv_unchanged_rs_body(process, process')
    { } 

    lemma lem_inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body_f_add_block_to_bn(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share_helper(
        s: ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>,
        id: Slot,
        proposer_duty: ProposerDuty,
        block_slashing_db: set<SlashingDBBlock>,
        complete_randao_reveal: BLSSignature,
        s': ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>
    )
    requires f_start_block_consensus_instance.requires(s, id, proposer_duty, block_slashing_db, complete_randao_reveal)
    requires s' == f_start_block_consensus_instance(s, id, proposer_duty, block_slashing_db, complete_randao_reveal)
    ensures s.active_consensus_instances.Keys + { id } == s'.active_consensus_instances.Keys
    { }  

    lemma lem_inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
        process: BlockDVCState,
        process': BlockDVCState
    )
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state
    requires inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process')
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
               && proposer_duty.slot !in process.block_consensus_engine_state.active_consensus_instances.Keys 
            {
                assert  && process'.current_proposer_duty.isPresent()
                        && process'.current_proposer_duty.safe_get() == process.current_proposer_duty.safe_get()
                        ;
                assert  process'.latest_proposer_duty.safe_get()
                        ==
                        process.latest_proposer_duty.safe_get();
                lem_inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share_helper(
                    process.block_consensus_engine_state,
                    proposer_duty.slot,
                    proposer_duty,
                    process.block_slashing_db,
                    constructed_randao_reveal.safe_get(),
                    process'.block_consensus_engine_state
                );

                var slot := proposer_duty.slot;

                forall k: Slot | k in process'.block_consensus_engine_state.slashing_db_hist.Keys
                ensures k < f_get_upperlimit_active_instances(process')
                {
                    if k in process.block_consensus_engine_state.slashing_db_hist.Keys
                    {
                        assert k < f_get_upperlimit_active_instances(process);
                    } 
                    else 
                    { 
                        assert k == slot;
                    }
                }
                
            }
            else 
            { }
        }
        else
        { }   
        
    }  

    lemma lem_inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process')
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }  

    lemma lem_inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state  
    requires inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)  
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process')
    { 
        var slot := proposer_duty.slot;
        if slot in process.future_consensus_instances_on_blocks_already_decided.Keys 
        { }
        else 
        {
            lem_inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
                process,
                process'
            );     
        }
    }  

    lemma lem_inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)  
    requires process.latest_proposer_duty.isPresent()
    requires f_get_upperlimit_active_instances(process) <= proposer_duty.slot + 1
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process')
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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
        lem_inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state  
    requires inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)  
    requires f_get_upperlimit_active_instances(process) <= proposer_duty.slot  
    ensures inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process')
    {
        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);
       
        lem_inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    }  

    lemma lem_inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock,        
        process': BlockDVCState
    )
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state
    requires inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)   
    ensures inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process') 
    { }        

    lemma lem_inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process)
    requires inv_active_consensus_instances_are_tracked_in_slashing_db_hist_body(process)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process')
    { 
        var new_consensus_instances_on_blocks_already_decided: map<Slot, BeaconBlock> := 
            map[ block.slot := block ];

        var consensus_instances_on_blocks_already_decided := process.future_consensus_instances_on_blocks_already_decided + new_consensus_instances_on_blocks_already_decided;

        var future_consensus_instances_on_blocks_already_decided := 
            f_listen_for_new_imported_blocks_helper(process, consensus_instances_on_blocks_already_decided);

        var process_after_stopping_consensus_instance :=
            process.(
                future_consensus_instances_on_blocks_already_decided := future_consensus_instances_on_blocks_already_decided,
                block_consensus_engine_state := f_stop_block_consensus_instances(
                                process.block_consensus_engine_state,
                                consensus_instances_on_blocks_already_decided.Keys
                ),
                block_shares_to_broadcast := process.block_shares_to_broadcast - consensus_instances_on_blocks_already_decided.Keys,
                rcvd_block_shares := process.rcvd_block_shares - consensus_instances_on_blocks_already_decided.Keys                    
            );  

        assert  inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process_after_stopping_consensus_instance); 

        if  && process_after_stopping_consensus_instance.current_proposer_duty.isPresent() 
            && process_after_stopping_consensus_instance.current_proposer_duty.safe_get().slot in consensus_instances_on_blocks_already_decided 
        {
            assert  process_after_stopping_consensus_instance.latest_proposer_duty.isPresent()
                    ==>
                    process'.latest_proposer_duty.isPresent()
                    ;
            assert  process'.latest_proposer_duty.isPresent();
            assert  process.latest_proposer_duty.safe_get()
                    ==
                    process_after_stopping_consensus_instance.latest_proposer_duty.safe_get()
                    ==
                    process'.latest_proposer_duty.safe_get()
                    ;
            assert  f_get_upperlimit_active_instances(process)
                    ==
                    f_get_upperlimit_active_instances(process_after_stopping_consensus_instance)
                    ==
                    f_get_upperlimit_active_instances(process')
                    ;

            var blocks := consensus_instances_on_blocks_already_decided[process.current_proposer_duty.safe_get().slot];
            var new_block_slashing_db := 
                f_update_block_slashing_db(process.block_slashing_db, block);      
            var new_active_consensus_instances := 
                f_update_block_consensus_instance_validity_check_states(
                    process.block_consensus_engine_state.active_consensus_instances,
                    new_block_slashing_db
                );      
            assert  new_active_consensus_instances.Keys
                    <=
                    process.block_consensus_engine_state.active_consensus_instances.Keys
                    ;

            var new_slashing_db_hist := 
                f_update_block_slashing_db_hist_with_new_consensus_instances_and_slashing_db_blocks(
                    process.block_consensus_engine_state.slashing_db_hist,
                    new_active_consensus_instances,
                    new_block_slashing_db
                );
            assert  new_slashing_db_hist.Keys 
                    ==
                    process.block_consensus_engine_state.slashing_db_hist.Keys + new_active_consensus_instances.Keys
                    ;
            assert  new_active_consensus_instances.Keys
                    <=
                    process.block_consensus_engine_state.active_consensus_instances.Keys
                    ;
            assert  process.block_consensus_engine_state.active_consensus_instances.Keys
                    <=
                    process.block_consensus_engine_state.slashing_db_hist.Keys
                    ;
                
            
            forall k: Slot | k in process'.block_consensus_engine_state.slashing_db_hist.Keys 
            ensures k < f_get_upperlimit_active_instances(process')
            {
                if k in process.block_consensus_engine_state.slashing_db_hist.Keys
                {
                    assert k < f_get_upperlimit_active_instances(process');
                }
                else
                {
                    assert k == process'.latest_proposer_duty.safe_get().slot;
                    assert k < f_get_upperlimit_active_instances(process');                    
                }
            }
            
            assert  inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process'); 
        }
        else
        {
            assert  inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process');
        }
    }  

    lemma lem_inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    requires inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body_f_resend_block_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state    
    requires inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_slot_of_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body_f_add_block_to_bn(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState,
        dv: BlockDVState,
        n: BLSPubkey
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block) 
    requires inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process)
    ensures inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process')
    { }      

    lemma lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState,
        dv: BlockDVState,
        n: BLSPubkey
    )
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state   
    requires inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process)
    ensures inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process')
    { }    

    lemma lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body_f_listen_for_randao_shares(
        process: BlockDVCState,
        randao_share: RandaoShare,
        process': BlockDVCState,
        dv: BlockDVState,
        n: BLSPubkey
    )
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process)
    ensures inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process')
    { }    

    lemma lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState,
        dv: BlockDVState,
        n: BLSPubkey
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state   
    requires inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process)
    ensures inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process')
    { }    

    lemma lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock,        
        process': BlockDVCState,
        dv: BlockDVState,
        n: BLSPubkey
    )
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state
    requires inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process)
    ensures inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process'); 
    { }  

    lemma lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        s': BlockDVCState,
        dv: BlockDVState,
        n: BLSPubkey
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires s' == f_check_for_next_duty(process, proposer_duty).state  
    requires inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process)
    ensures inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, s')
    { } 



    lemma lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        s': BlockDVCState,
        dv: BlockDVState,
        n: BLSPubkey
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires s' == f_listen_for_new_imported_blocks(process, block).state       
    requires inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process)
    requires && dv.consensus_instances_on_beacon_block[block.slot].decided_value.isPresent()
             && block == dv.consensus_instances_on_beacon_block[block.slot].decided_value.safe_get()
    ensures inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, s');
    { }      

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_add_block_to_bn(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
    { }

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_start_consensus_if_can_construct_randao_share(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
    { }      

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
    { }

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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

        lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
    {
        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);
       
        lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );
    } 

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        block: BeaconBlock, 
        process': BlockDVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
    { }  

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
    { }

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
    { }  

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
    { }  

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_resend_block_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state    
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
    { }

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_add_block_to_bn(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process')
    { }

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_start_consensus_if_can_construct_randao_share(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process')
    { }      

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process')
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process')
    { }

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process')
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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

        lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process')
    {
        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);
       
        lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );
    } 

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        block: BeaconBlock, 
        process': BlockDVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    requires inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process')
    { 
        if && process.current_proposer_duty.isPresent()
           && process.current_proposer_duty.safe_get().slot == block.slot
           && id == block.slot
        {
            assert  process.latest_proposer_duty.isPresent();            
        }
        else
        { }
    }  

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process')
    { }

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(process)
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process')
    { 
        var new_consensus_instances_on_blocks_already_decided: map<Slot, BeaconBlock> := 
            map[ block.slot := block ];

        var consensus_instances_on_blocks_already_decided := process.future_consensus_instances_on_blocks_already_decided + new_consensus_instances_on_blocks_already_decided;

        var future_consensus_instances_on_blocks_already_decided := 
            f_listen_for_new_imported_blocks_helper(process, consensus_instances_on_blocks_already_decided);

        var process_after_stopping_consensus_instance :=
                process.(
                    future_consensus_instances_on_blocks_already_decided := future_consensus_instances_on_blocks_already_decided,
                    block_consensus_engine_state := f_stop_block_consensus_instances(
                                    process.block_consensus_engine_state,
                                    consensus_instances_on_blocks_already_decided.Keys
                    ),
                    block_shares_to_broadcast := process.block_shares_to_broadcast - consensus_instances_on_blocks_already_decided.Keys,
                    rcvd_block_shares := process.rcvd_block_shares - consensus_instances_on_blocks_already_decided.Keys                    
                );   

        if  && process_after_stopping_consensus_instance.current_proposer_duty.isPresent() 
            && process_after_stopping_consensus_instance.current_proposer_duty.safe_get().slot in consensus_instances_on_blocks_already_decided
        {
            assert  process_after_stopping_consensus_instance.latest_proposer_duty.isPresent();
        }
        else
        { }
    }  

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process')
    { }  

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_resend_block_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state    
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process')
    { }  

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body_f_add_block_to_bn(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process')
    { } 

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process')
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    } 

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires && process.latest_proposer_duty.isPresent()
             && process.latest_proposer_duty.safe_get().slot == proposer_duty.slot
    requires inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process)
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process')
    { 
        var slot := proposer_duty.slot;
        if slot in process.future_consensus_instances_on_blocks_already_decided.Keys
        {
            var block := process.future_consensus_instances_on_blocks_already_decided[slot];     
            assert  block.slot == slot;

            var block_slashing_db := process.block_slashing_db;
            var new_block_slashing_db := 
                f_update_block_slashing_db(process.block_slashing_db, block);  

            var new_slashingDB_block := construct_SlashingDBBlock_from_beacon_block(block);        
            assert  && block_slashing_db + {new_slashingDB_block} == new_block_slashing_db
                    && new_slashingDB_block.slot == block.slot
                    ;

            forall  slashing_db_block: SlashingDBBlock | slashing_db_block in new_block_slashing_db
            ensures slashing_db_block.slot <= slot
            {
                if slashing_db_block in block_slashing_db
                {
                    assert  slashing_db_block.slot <= slot;
                }
                else
                {
                    assert  slashing_db_block == new_slashingDB_block;
                    assert  slashing_db_block.slot <= slot;
                }
            }            

            assert  inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process');
        }
        else 
        {
            lem_inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
                process,
                process'
            );
        }
            
    }

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process)
    requires && process.latest_proposer_duty.isPresent()
             && process.latest_proposer_duty.safe_get().slot == proposer_duty.slot
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process')
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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

        lem_inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    requires inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process)
    requires inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty_body(process, proposer_duty)
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process')
    {
        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);

        assert  process_after_receiving_duty.latest_proposer_duty.isPresent();                

        assert  process_after_receiving_duty.block_slashing_db
                ==
                process.block_slashing_db
                ;

        if  !process.latest_proposer_duty.isPresent()
        {
            assert  process_after_receiving_duty.block_slashing_db == {};
            assert  inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process_after_receiving_duty);
        }
        else
        {
            assert  inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process_after_receiving_duty);
        }
       
        lem_inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );
    } 

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        block: BeaconBlock, 
        process': BlockDVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    requires inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process')
    { 
        if && process.current_proposer_duty.isPresent()
           && process.current_proposer_duty.safe_get().slot == block.slot
           && id == block.slot
        {
            var slot := block.slot;
            var new_slashingDB_block := construct_SlashingDBBlock_from_beacon_block(block);   
            var block_slashing_db := process.block_slashing_db;
            var new_block_slashing_db := f_update_block_slashing_db(process.block_slashing_db, block);
            assert  && block_slashing_db + {new_slashingDB_block} == new_block_slashing_db
                    && new_slashingDB_block.slot == block.slot
                    ;

            forall slashing_db_block: SlashingDBBlock | slashing_db_block in new_block_slashing_db
            ensures slashing_db_block.slot <= block.slot
            {
                if slashing_db_block in block_slashing_db
                {
                    assert  slashing_db_block.slot <= slot;
                }
                else
                {
                    assert  slashing_db_block == new_slashingDB_block;
                    assert  slashing_db_block.slot <= slot;
                }
            }

            var block_signing_root := compute_block_signing_root(block);
            var fork_version := af_bn_get_fork_version(block.slot);
            var block_signature := af_rs_sign_block(block, fork_version, block_signing_root, process.rs);
            var block_share := SignedBeaconBlock(block, block_signature);
            var process_after_updating_block_shares_to_broadcast := 
                process.(                
                    block_shares_to_broadcast := process.block_shares_to_broadcast[slot := block_share],
                    block_slashing_db := new_block_slashing_db,
                    block_consensus_engine_state := f_update_block_consensus_engine_state(
                                                        process.block_consensus_engine_state,
                                                        new_block_slashing_db
                                                    ),
                    latest_slashing_db_block := Some(new_slashingDB_block)
                );
            
        }
        else
        { }
    }  

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    requires inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process')
    { 
        var new_consensus_instances_on_blocks_already_decided: map<Slot, BeaconBlock> := 
            map[ block.slot := block ];

        var consensus_instances_on_blocks_already_decided := process.future_consensus_instances_on_blocks_already_decided + new_consensus_instances_on_blocks_already_decided;

        var future_consensus_instances_on_blocks_already_decided := 
            f_listen_for_new_imported_blocks_helper(process, consensus_instances_on_blocks_already_decided);

        var process_after_stopping_consensus_instance :=
                process.(
                    future_consensus_instances_on_blocks_already_decided := future_consensus_instances_on_blocks_already_decided,
                    block_consensus_engine_state := f_stop_block_consensus_instances(
                                    process.block_consensus_engine_state,
                                    consensus_instances_on_blocks_already_decided.Keys
                    ),
                    block_shares_to_broadcast := process.block_shares_to_broadcast - consensus_instances_on_blocks_already_decided.Keys,
                    rcvd_block_shares := process.rcvd_block_shares - consensus_instances_on_blocks_already_decided.Keys                    
                );   

        if  && process_after_stopping_consensus_instance.current_proposer_duty.isPresent() 
            && process_after_stopping_consensus_instance.current_proposer_duty.safe_get().slot in consensus_instances_on_blocks_already_decided 
        {
            var slot := process_after_stopping_consensus_instance.current_proposer_duty.safe_get().slot;
            var decided_beacon_blocks := consensus_instances_on_blocks_already_decided[process.current_proposer_duty.safe_get().slot];
            var block_slashing_db := process.block_slashing_db;
            var new_block_slashing_db := f_update_block_slashing_db(process.block_slashing_db, decided_beacon_blocks);
            var new_slashingDB_block := construct_SlashingDBBlock_from_beacon_block(decided_beacon_blocks);  
            
            assert  block_slashing_db + {new_slashingDB_block} == new_block_slashing_db;

            assert  new_slashingDB_block.slot == decided_beacon_blocks.slot;

            forall  slashing_db_block: SlashingDBBlock | slashing_db_block in new_block_slashing_db
            ensures slashing_db_block.slot <= slot
            {
                if slashing_db_block in block_slashing_db
                {
                    assert  slashing_db_block.slot <= slot;
                }
                else
                {
                    assert  slashing_db_block == new_slashingDB_block;
                    assert  slashing_db_block.slot <= slot;
                }
            }            

            assert  inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process');
        }
        else
        { 
            assert  inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process');
        }
    }  

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    requires inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body_f_resend_block_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state    
    requires inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_add_block_to_bn(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
    { }

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_start_consensus_if_can_construct_randao_share(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
    { }      

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
    { }

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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

        lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
    {
        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);
       
        lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );
    } 

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        block: BeaconBlock, 
        process': BlockDVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
    { }  

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
    { }

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
    { }  

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
    { }  

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_resend_block_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state    
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
    { }  

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body_f_add_block_to_bn(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process')
    { }

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body_f_start_consensus_if_can_construct_randao_share(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process')
    { }      

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body_f_listen_for_randao_shares(
        process: BlockDVCState, 
        randao_share: RandaoShare,
        process': BlockDVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process')
    { 
        var slot := randao_share.slot;
        var active_consensus_instances := process.block_consensus_engine_state.active_consensus_instances.Keys;

        if is_slot_for_current_or_future_instances(process, slot) 
        {
            var process_with_new_randao_share := 
                process.(
                    rcvd_randao_shares := process.rcvd_randao_shares[slot := get_or_default(process.rcvd_randao_shares, slot, {}) + 
                                                                                    {randao_share} ]
                );   
            lem_inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body_f_check_for_next_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires && process.latest_proposer_duty.isPresent()
             && process.latest_proposer_duty.safe_get().slot <= proposer_duty.slot
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    requires inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process)
    requires inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process')
    { 
        var slot := proposer_duty.slot;
        if slot in process.future_consensus_instances_on_blocks_already_decided.Keys 
        {
            var block := process.future_consensus_instances_on_blocks_already_decided[slot];                
            var new_slashingDB_block := construct_SlashingDBBlock_from_beacon_block(block);
            var block_slashing_db := process.block_slashing_db;
            var new_block_slashing_db := f_update_block_slashing_db(process.block_slashing_db, block);           

            assert  process'.latest_slashing_db_block.isPresent();
            assert  process'.latest_slashing_db_block.safe_get().slot == slot;

            forall  slashing_db_block: SlashingDBBlock | slashing_db_block in new_block_slashing_db
            ensures slashing_db_block.slot <= slot
            {
                if slashing_db_block in block_slashing_db
                {
                    assert  slashing_db_block.slot <= slot;
                }
                else
                {
                    assert  slashing_db_block == new_slashingDB_block;
                    assert  slashing_db_block.slot <= slot;
                }
            }  

            assert inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process');
        }
        else 
        { }
    }

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body_f_broadcast_randao_share(
        process: BlockDVCState,
        proposer_duty: ProposerDuty, 
        process': BlockDVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires && process.latest_proposer_duty.isPresent()
             && process.latest_proposer_duty.safe_get().slot <= proposer_duty.slot
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    requires inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process)
    requires inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process')
    { 
        var slot := proposer_duty.slot;
        var fork_version := af_bn_get_fork_version(slot);    
        var epoch := compute_epoch_at_slot(slot);
        var randao_reveal_signing_root := compute_randao_reveal_signing_root(slot);
        var randao_reveal_signature_share := af_rs_sign_randao_reveal(epoch, fork_version, randao_reveal_signing_root, process.rs);
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

        lem_inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body_f_serve_proposer_duty(
        process: BlockDVCState,
        proposer_duty: ProposerDuty,
        process': BlockDVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty_body(process, proposer_duty)
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    requires inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process)
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    requires inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process')
    {
        assert  inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process);
        
        if process.latest_proposer_duty.isPresent()
        {
            assert  process.latest_proposer_duty.safe_get().slot < proposer_duty.slot;
        }

        var process_after_receiving_duty := 
            f_receive_new_duty(process, proposer_duty);
        var slot := proposer_duty.slot;

        assert  && process_after_receiving_duty.latest_proposer_duty.isPresent()
                && process_after_receiving_duty.latest_proposer_duty.safe_get().slot == slot
                ;
        assert  inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process_after_receiving_duty);

        forall slashing_db_block | slashing_db_block in process_after_receiving_duty.block_slashing_db
        ensures slashing_db_block.slot < slot;
        {
            assert  slashing_db_block in process.block_slashing_db;
            assert  slashing_db_block in process.block_slashing_db;
            assert  process.latest_proposer_duty.isPresent();
            assert  slashing_db_block.slot <= process.latest_proposer_duty.safe_get().slot;
            assert  slashing_db_block.slot < slot;
        }

        assert  inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process_after_receiving_duty);        
       
        lem_inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );
    } 

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body_f_block_consensus_decided(
        process: BlockDVCState,
        id: Slot,
        block: BeaconBlock, 
        process': BlockDVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    requires inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    requires inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process')
    { 
        if && process.current_proposer_duty.isPresent()
           && process.current_proposer_duty.safe_get().slot == block.slot
           && id == block.slot
        {
            var slot := block.slot;            

            assert  && process'.latest_proposer_duty.isPresent()
                    && process'.latest_proposer_duty.safe_get().slot == slot;
            assert  && process'.latest_slashing_db_block.isPresent()
                    && process'.latest_slashing_db_block.safe_get().slot == slot;

            lem_inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body_f_block_consensus_decided(
                process, 
                id, 
                block, 
                process'
            );               
        }
        else
        { }
    }  

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body_f_listen_for_block_signature_shares(
        process: BlockDVCState,
        block_share: SignedBeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process')
    { }

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body_f_listen_for_new_imported_blocks(
        process: BlockDVCState,
        block: BeaconBlock,
        process': BlockDVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    requires inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body(process)
    requires inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process')
    { 
        var new_consensus_instances_on_blocks_already_decided: map<Slot, BeaconBlock> := 
            map[ block.slot := block ];

        var consensus_instances_on_blocks_already_decided := process.future_consensus_instances_on_blocks_already_decided + new_consensus_instances_on_blocks_already_decided;

        var future_consensus_instances_on_blocks_already_decided := 
            f_listen_for_new_imported_blocks_helper(process, consensus_instances_on_blocks_already_decided);

        var process_after_stopping_consensus_instance :=
            process.(
                future_consensus_instances_on_blocks_already_decided := future_consensus_instances_on_blocks_already_decided,
                block_consensus_engine_state := f_stop_block_consensus_instances(
                                process.block_consensus_engine_state,
                                consensus_instances_on_blocks_already_decided.Keys
                ),
                block_shares_to_broadcast := process.block_shares_to_broadcast - consensus_instances_on_blocks_already_decided.Keys,
                rcvd_block_shares := process.rcvd_block_shares - consensus_instances_on_blocks_already_decided.Keys                    
            );   

        if  && process_after_stopping_consensus_instance.current_proposer_duty.isPresent() 
            && process_after_stopping_consensus_instance.current_proposer_duty.safe_get().slot in consensus_instances_on_blocks_already_decided 
        { 
            var slot := process_after_stopping_consensus_instance.current_proposer_duty.safe_get().slot;
            var decided_beacon_blocks := consensus_instances_on_blocks_already_decided[process.current_proposer_duty.safe_get().slot];
            var new_slashingDB_block := construct_SlashingDBBlock_from_beacon_block(decided_beacon_blocks);
            
            lem_inv_slots_in_slashing_db_is_not_higher_than_slot_of_latest_proposer_duty_body_f_listen_for_new_imported_blocks(
                process, 
                block, 
                process'
            );

            assert  new_slashingDB_block.slot == slot;
            assert  && process'.latest_proposer_duty.isPresent()
                    && process'.latest_proposer_duty.safe_get().slot == slot
                    ;
            assert  && process'.latest_slashing_db_block.isPresent()
                    && process'.latest_slashing_db_block.safe_get().slot == slot;
        }        
        else
        { }
    }  

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body_f_resend_randao_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_randao_shares.requires(process)
    requires process' == f_resend_randao_shares(process).state    
    requires inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process')
    { }  

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body_f_resend_block_shares(
        process: BlockDVCState, 
        process': BlockDVCState)
    requires f_resend_block_shares.requires(process)
    requires process' == f_resend_block_shares(process).state    
    requires inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_slot_of_latest_slashing_db_block_body(process')
    { }  
}