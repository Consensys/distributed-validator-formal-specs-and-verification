include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../../../../specs/dv/dv_block_proposer.dfy"
include "../inv.dfy"
include "../../../common/helper_sets_lemmas.dfy"
include "../../common/common_proofs.dfy"
include "../../common/block_dvc_spec_axioms.dfy"

include "../../../../common/commons.dfy"

include "../../common/dvc_block_proposer_instrumented.dfy"
include "../../../../specs/consensus/consensus.dfy"
include "../../../../specs/network/network.dfy"
include "../inv.dfy"
include "../../../common/helper_sets_lemmas.dfy"



include "invs_fnc_1.dfy"



module Fnc_Invs_2
{
    import opened Types 
    
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DV_Block_Proposer_Spec
    import opened DVC_Block_Proposer_Spec_Instr
    import opened Block_Consensus_Engine_Instr
    import opened Block_Inv_With_Empty_Initial_Block_Slashing_DB
    import opened Helper_Sets_Lemmas
    import opened Common_Proofs_For_Block_Proposer
    import opened DVC_Block_Proposer_Spec_Axioms
    
    import opened Fnc_Invs_1
    
    lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_ces_f_check_for_next_duty_known_decision(
        process: DVCState,
        proposer_duty: ProposerDuty,
        block: BeaconBlock
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process)
    requires proposer_duty.slot in process.future_consensus_instances_on_blocks_already_decided.Keys
    requires block == process.future_consensus_instances_on_blocks_already_decided[proposer_duty.slot]
    ensures && var new_block_slashing_db := 
                    f_update_block_slashing_db(
                        process.block_slashing_db, 
                        block
                    );
            && inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_ces(
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
        assert inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_ces(
                            process.block_consensus_engine_state, 
                            process.block_slashing_db); 

        forall s: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> |
                            ( && s  in process.block_consensus_engine_state.block_slashing_db_hist.Keys
                            && vp in process.block_consensus_engine_state.block_slashing_db_hist[s]
                            && db in process.block_consensus_engine_state.block_slashing_db_hist[s][vp]
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

        assert inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_ces(
                        process.block_consensus_engine_state, 
                        new_block_slashing_db);
    }

    lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(s)
    ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(s')
    { }

    lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process)
    ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process')
    { }

    lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process)
    ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process')
    { }      

    lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process)
    ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process')
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
            lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process)
    ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process')
    { 
        var slot := proposer_duty.slot;
        if slot in process.future_consensus_instances_on_blocks_already_decided 
        {
            var block := process.future_consensus_instances_on_blocks_already_decided[slot];                
            var new_block_slashing_db := 
                f_update_block_slashing_db(process.block_slashing_db, block);            
            assert  inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_ces(
                            process.block_consensus_engine_state, 
                            process.block_slashing_db); 

            var slashing_db_block := construct_SlashingDBBlock_from_beacon_block(block);
            
            lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_ces_f_check_for_next_duty_known_decision(
                process,
                proposer_duty,
                block
            );
        }
        else
        {
            lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_start_consensus_if_can_construct_randao_share(
                process, 
                process'
            );
        }
    }

    lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process)
    ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process')
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

        lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process)
    ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_rcvd_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_broadcast_randao_share(
            process_rcvd_duty,
            proposer_duty,
            process'
        );    
    } 

    lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process)
    ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process')
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
                ( && s in process'.block_consensus_engine_state.block_slashing_db_hist.Keys
                  && vp in process'.block_consensus_engine_state.block_slashing_db_hist[s].Keys
                  && db in process'.block_consensus_engine_state.block_slashing_db_hist[s][vp]
                )
            ensures db <= process'.block_slashing_db
            {
                if  && s in process.block_consensus_engine_state.block_slashing_db_hist.Keys
                    && vp in process.block_consensus_engine_state.block_slashing_db_hist[s].Keys
                    && db in process.block_consensus_engine_state.block_slashing_db_hist[s][vp]
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

    lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process)
    ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process')
    { }

    lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process)
    ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process')
    { 
        var new_consensus_instances_on_blocks_already_decided: map<Slot, BeaconBlock> := 
            map[ block.slot := block ];

        var consensus_instances_on_blocks_already_decided := process.future_consensus_instances_on_blocks_already_decided + new_consensus_instances_on_blocks_already_decided;

        var future_consensus_instances_on_blocks_already_decided := 
            f_listen_for_new_imported_blocks_helper(process, consensus_instances_on_blocks_already_decided);

        var process_after_stopping_consensus_instance :=
            process.(
                future_consensus_instances_on_blocks_already_decided := future_consensus_instances_on_blocks_already_decided,
                block_consensus_engine_state := stopConsensusInstances(
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
            assert inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_ces(process_after_stopping_consensus_instance.block_consensus_engine_state, 
                              process.block_slashing_db); 

            forall s: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> |
                            ( && s  in process_after_stopping_consensus_instance.block_consensus_engine_state.block_slashing_db_hist.Keys
                              && vp in process_after_stopping_consensus_instance.block_consensus_engine_state.block_slashing_db_hist[s]
                              && db in process_after_stopping_consensus_instance.block_consensus_engine_state.block_slashing_db_hist[s][vp]
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
            assert inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process);
        }
    }  

    lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process)
    ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process')
    { }  

    lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process)
    ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process')
    { }  
    
    lemma lem_multicast_getMessagesFromMessagesWithRecipient(process: DVCState, block_with_signature_share: SignedBeaconBlock)
    requires |process.peers| > 0    
    ensures getMessagesFromMessagesWithRecipient(multicast(block_with_signature_share, process.peers))
            ==
            { block_with_signature_share }            
    {
        var mcast_msgs := multicast(block_with_signature_share, process.peers);
        assert (forall msg | msg in mcast_msgs :: msg.message == block_with_signature_share);
        assert |mcast_msgs| > 0;
        
        var msgs_content := getMessagesFromMessagesWithRecipient(mcast_msgs);
        

        var all_mcast_msgs := mcast_msgs;
        var checked_mcast_msgs := {};

        while all_mcast_msgs != {}            
            invariant all_mcast_msgs + checked_mcast_msgs == mcast_msgs
            invariant   checked_mcast_msgs == {}
                        ==> 
                        getMessagesFromMessagesWithRecipient(checked_mcast_msgs) == {}
            invariant   checked_mcast_msgs != {}
                        ==> 
                        getMessagesFromMessagesWithRecipient(checked_mcast_msgs) == { block_with_signature_share } 
            decreases |all_mcast_msgs|
        {
            var msg :|  msg in all_mcast_msgs;
            assert msg.message ==  block_with_signature_share;
            all_mcast_msgs := all_mcast_msgs - {msg};
            checked_mcast_msgs := checked_mcast_msgs + {msg};
        }        

        assert getMessagesFromMessagesWithRecipient(mcast_msgs) == { block_with_signature_share };
    }

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    ensures process'.block_shares_to_broadcast == process.block_shares_to_broadcast
    ensures process'.peers == process.peers         
    { }

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    ensures process'.block_shares_to_broadcast == process.block_shares_to_broadcast
    ensures process'.peers == process.peers         
    { }

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    ensures process'.block_shares_to_broadcast == process.block_shares_to_broadcast
    ensures process'.peers == process.peers       
    { }      

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    ensures process'.block_shares_to_broadcast == process.block_shares_to_broadcast
    ensures process'.peers == process.peers       
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
            lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }     

     lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    ensures process'.block_shares_to_broadcast == process.block_shares_to_broadcast
    ensures process'.peers == process.peers     
    { }

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    ensures process'.block_shares_to_broadcast == process.block_shares_to_broadcast
    ensures process'.peers == process.peers
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

        lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    ensures process'.block_shares_to_broadcast == process.block_shares_to_broadcast
    ensures process'.peers == process.peers
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);

        lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);

        lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    ensures process'.block_shares_to_broadcast == process.block_shares_to_broadcast
    ensures process'.peers == process.peers
    { }

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    ensures process'.block_shares_to_broadcast.Values <= process.block_shares_to_broadcast.Values
    ensures process'.peers == process.peers
    { }  

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    ensures process'.block_shares_to_broadcast == process.block_shares_to_broadcast
    ensures process'.peers == process.peers
    { }  

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    ensures process'.block_shares_to_broadcast == process.block_shares_to_broadcast
    ensures process'.peers == process.peers
    { }  

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock, 
        process': DVCState,
        outputs: Outputs
    )
    requires |process.peers| > 0
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state         
    requires outputs == f_block_consensus_decided(process, id, decided_beacon_block).outputs    
    requires decided_beacon_block.slot == id  
    ensures (process'.block_shares_to_broadcast.Values - process.block_shares_to_broadcast.Values) <= getMessagesFromMessagesWithRecipient(outputs.sent_block_shares);
    {   
        if  && process.current_proposer_duty.isPresent()
            && process.current_proposer_duty.safe_get().slot == decided_beacon_block.slot
            && id == decided_beacon_block.slot
        {
           var new_block_slashing_db := f_update_block_slashing_db(process.block_slashing_db, decided_beacon_block);
            var block_signing_root := compute_block_signing_root(decided_beacon_block);
            var fork_version := bn_get_fork_version(decided_beacon_block.slot);
            var block_signature := rs_sign_block(decided_beacon_block, fork_version, block_signing_root, process.rs);
            var block_share := SignedBeaconBlock(decided_beacon_block, block_signature);
            var slot := decided_beacon_block.slot;

            lem_multicast_getMessagesFromMessagesWithRecipient(process', block_share);
        }
        else
        {
        }
    }

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    ensures s'.rcvd_block_shares == s.rcvd_block_shares 
    { }

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    ensures process'.rcvd_block_shares == process.rcvd_block_shares 
    { }

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_start_consensus_if_can_construct_randao_share(process: DVCState, process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state       
    ensures process'.rcvd_block_shares == process.rcvd_block_shares
    { } 

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    ensures process'.rcvd_block_shares == process.rcvd_block_shares
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
            lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    } 

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state        
    ensures process'.rcvd_block_shares == process.rcvd_block_shares
    { }

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    ensures process'.rcvd_block_shares == process.rcvd_block_shares
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

        lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    ensures process'.rcvd_block_shares == process.rcvd_block_shares
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);

        lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);

        lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    ensures process'.rcvd_block_shares == process.rcvd_block_shares
    { }  

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
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
                                &&  var rcvd_block_shares_db_at_slot := getOrDefault(process.rcvd_block_shares, slot, map[]);

                                &&  process'.rcvd_block_shares[i][j] 
                                    <= 
                                     getOrDefault(rcvd_block_shares_db_at_slot, data, {}) + {block_share} 
                           )
                   )                                      
    { }

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
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
    
    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    ensures process'.rcvd_block_shares == process.rcvd_block_shares
    { }  

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_resend_block_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state        
    ensures process'.rcvd_block_shares == process.rcvd_block_shares
    { } 

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_body_f_listen_for_block_signature_shares_domain(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
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
        var activate_block_consensus_intances := process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys;
        var slot := block_share.block.slot;

        if  is_slot_for_current_or_future_instances(process, slot) 
        {
            var block_shares_db_at_slot := getOrDefault(process.rcvd_block_shares, block_share.block.slot, map[]);
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

            var new_set := getOrDefault(block_shares_db_at_slot, data, {}) + {block_share};
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


    // lemma lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_add_block_to_bn(
    //     s: DVCState,
    //     block: BeaconBlock,
    //     s': DVCState 
    // )
    // requires f_add_block_to_bn.requires(s, block)
    // requires s' == f_add_block_to_bn(s, block)    
    // requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(s)
    // ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(s')
    // { }

    // lemma lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_listen_for_block_signature_shares(
    //     process: DVCState,
    //     block_share: SignedBeaconBlock,
    //     process': DVCState
    // )
    // requires f_listen_for_block_signature_shares.requires(process, block_share)
    // requires process' == f_listen_for_block_signature_shares(process, block_share).state        
    // requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process)
    // ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process')
    // { }

    // lemma lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_start_consensus_if_can_construct_randao_share(
    //     process: DVCState, 
    //     proposer_duty: ProposerDuty, 
    //     process': DVCState)
    // requires f_start_consensus_if_can_construct_randao_share.requires(process)
    // requires process' == f_start_consensus_if_can_construct_randao_share(process).state   
    // requires proposer_duty in process.all_rcvd_duties
    // requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process)
    // ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process')
    // { } 

    // lemma lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_resend_block_share(
    //     process: DVCState,
    //     process': DVCState)
    // requires f_resend_block_share.requires(process)
    // requires process' == f_resend_block_share(process).state        
    // requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process)
    // ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process')
    // { } 

    // lemma lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_check_for_next_duty(
    //     process: DVCState,
    //     proposer_duty: ProposerDuty,
    //     process': DVCState
    // )
    // requires f_check_for_next_duty.requires(process, proposer_duty)
    // requires process' == f_check_for_next_duty(process, proposer_duty).state    
    // requires inv_consensus_instance_only_for_slot_in_which_process_has_rcvd_proposer_duty_body(process)
    // requires proposer_duty in process.all_rcvd_duties
    // requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process)
    // ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process')
    // { 
    //     if proposer_duty.slot in process.future_consensus_instances_on_blocks_already_decided.Keys 
    //     {
    //     }
    //     else
    //     {
    //         lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_start_consensus_if_can_construct_randao_share(
    //             process, 
    //             proposer_duty, 
    //             process'
    //         );
    //     }
    // }

    // lemma lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_block_consensus_decided(
    //     process: DVCState,
    //     id: Slot,
    //     decided_beacon_block: BeaconBlock, 
    //     process': DVCState
    // )
    // requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    // requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state         
    // requires inv_consensus_instance_only_for_slot_in_which_process_has_rcvd_proposer_duty_body(process)
    // requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process)
    // ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process')
    // { }

    // lemma lem_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_terminate_current_proposer_duty(
    //     process: DVCState,
    //     process': DVCState
    // )
    // requires f_terminate_current_proposer_duty.requires(process)
    // requires process' == f_terminate_current_proposer_duty(process)
    // requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process)
    // ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process')
    // { }

    // lemma lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_serve_proposer_duty(
    //     process: DVCState,
    //     proposer_duty: ProposerDuty,
    //     process': DVCState
    // )  
    // requires f_serve_proposer_duty.requires(process, proposer_duty)
    // requires process' == f_serve_proposer_duty(process, proposer_duty).state
    // requires inv_consensus_instance_only_for_slot_in_which_process_has_rcvd_proposer_duty_body(process)
    // requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process)
    // ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process')
    // {
    //     var process_rcvd_duty := 
    //             process.(all_rcvd_duties := process.all_rcvd_duties + {proposer_duty});
    //     var process_after_stopping_active_consensus_instance := f_terminate_current_proposer_duty(process_rcvd_duty);
    //     lem_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_terminate_current_proposer_duty(
    //         process_rcvd_duty,
    //         process_after_stopping_active_consensus_instance
    //     );
    //     lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_check_for_next_duty(
    //         process_after_stopping_active_consensus_instance,
    //         proposer_duty,
    //         process'
    //     );           
    // }

    // lemma lem_inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body_f_listen_for_new_imported_blocks(
    //     process: DVCState,
    //     block: BeaconBlock,
    //     process': DVCState
    // )
    // requires f_listen_for_new_imported_blocks.requires(process, block)
    // requires process' == f_listen_for_new_imported_blocks(process, block).state        
    // requires inv_consensus_instance_only_for_slot_in_which_process_has_rcvd_proposer_duty_body(process)
    // requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process)
    // ensures inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(process')
    // { }  


    lemma lem_inv_block_slashing_db_is_monotonic_body_f_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    ensures inv_block_slashing_db_is_monotonic_body(s, s') 
    { }

    lemma lem_inv_block_slashing_db_is_monotonic_body_f_terminate_current_proposer_duty(
        s: DVCState,
        s': DVCState 
    )
    requires f_terminate_current_proposer_duty.requires(s)
    requires s' == f_terminate_current_proposer_duty(s)    
    ensures inv_block_slashing_db_is_monotonic_body(s, s') 
    { }

    lemma lem_inv_block_slashing_db_is_monotonic_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state        
    ensures inv_block_slashing_db_is_monotonic_body(process, process')
    { }

    lemma lem_inv_block_slashing_db_is_monotonic_body_f_start_consensus_if_can_construct_randao_share(process: DVCState, process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state       
    ensures inv_block_slashing_db_is_monotonic_body(process, process')
    { } 

    lemma lem_inv_block_slashing_db_is_monotonic_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    ensures inv_block_slashing_db_is_monotonic_body(process, process')
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
            lem_inv_block_slashing_db_is_monotonic_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    } 

    lemma lem_inv_block_slashing_db_is_monotonic_body_f_resend_block_share(
        process: DVCState,
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state        
    ensures inv_block_slashing_db_is_monotonic_body(process, process')    
    { } 

    lemma lem_inv_block_slashing_db_is_monotonic_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state        
    ensures inv_block_slashing_db_is_monotonic_body(process, process')
    { }

    lemma lem_inv_block_slashing_db_is_monotonic_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    ensures inv_block_slashing_db_is_monotonic_body(process, process')
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

        lem_inv_block_slashing_db_is_monotonic_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_block_slashing_db_is_monotonic_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state         
    ensures inv_block_slashing_db_is_monotonic_body(process, process')
    { }

    lemma lem_inv_block_slashing_db_is_monotonic_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    ensures inv_block_slashing_db_is_monotonic_body(process, process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);

        lem_inv_block_slashing_db_is_monotonic_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);

        lem_inv_block_slashing_db_is_monotonic_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );        
    }

    lemma lem_inv_block_slashing_db_is_monotonic_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    ensures inv_block_slashing_db_is_monotonic_body(process, process')
    { }

    lemma lem_inv_block_slashing_db_is_monotonic_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state   
    ensures inv_block_slashing_db_is_monotonic_body(process, process')
    { } 

    lemma lem_inv_block_slashing_db_is_monotonic_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    ensures inv_block_slashing_db_is_monotonic_body(process, process')
    { }  

    

    // lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_add_block_to_bn(
    //     s: DVCState,
    //     block: BeaconBlock,
    //     s': DVCState 
    // )
    // requires f_add_block_to_bn.requires(s, block)
    // requires s' == f_add_block_to_bn(s, block)    
    // requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(s)
    // ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(s')
    // { }

    // lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_listen_for_block_signature_shares(
    //     process: DVCState,
    //     block_share: SignedBeaconBlock,
    //     process': DVCState
    // )
    // requires f_listen_for_block_signature_shares.requires(process, block_share)
    // requires process' == f_listen_for_block_signature_shares(process, block_share).state        
    // requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process)
    // ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process')
    // { }

    // lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_start_consensus_if_can_construct_randao_share(
    //     process: DVCState, 
    //     proposer_duty: ProposerDuty, 
    //     process': DVCState)
    // requires f_start_consensus_if_can_construct_randao_share.requires(process)
    // requires process' == f_start_consensus_if_can_construct_randao_share(process).state   
    // requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process)
    // ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process')
    // { } 

    // lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_resend_block_share(
    //     process: DVCState,
    //     process': DVCState)
    // requires f_resend_block_share.requires(process)
    // requires process' == f_resend_block_share(process).state        
    // requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process)
    // ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process')
    // { } 

    

    // lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_check_for_next_duty(
    //     process: DVCState,
    //     proposer_duty: ProposerDuty,
    //     process': DVCState
    // )
    // requires f_check_for_next_duty.requires(process, proposer_duty)
    // requires process' == f_check_for_next_duty(process, proposer_duty).state    
    // requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)    
    // requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process)
    // ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process')
    // { 
    //     if pred_decision_of_proposer_duty_was_known(process, proposer_duty)
    //     {
    //         assert inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_ces(
    //                         process.block_consensus_engine_state, 
    //                         process.block_slashing_db); 

    //         var block := process.future_consensus_instances_on_blocks_already_decided[proposer_duty.slot];      
            
    //         var slashing_db_block := SlashingDBBlock(
    //                                         source_epoch := block.source.epoch,
    //                                         target_epoch := block.target.epoch,
    //                                         signing_root := Some(hash_tree_root(block)));

    //         lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_ces_f_check_for_next_duty_known_decision(
    //             process,
    //             proposer_duty,
    //             block
    //         );
    //     }
    //     else
    //     {
    //         lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_start_consensus_if_can_construct_randao_share(
    //             process, 
    //             proposer_duty, 
    //             process'
    //         );
    //     }
    // }

    // lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_ces_f_block_consensus_decided(
    //     process: DVCState,
    //     id: Slot,
    //     decided_beacon_block: BeaconBlock
    // )
    // requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    // requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process)
    // requires is_decided_data_for_current_slot(process, decided_beacon_block, id)
    // ensures && var block_slashing_db := f_update_block_slashing_db(process.block_slashing_db, decided_beacon_block);
    //         && inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_ces(process.block_consensus_engine_state, 
    //                         block_slashing_db)
    // {
    //     var local_current_proposer_duty := process.current_proposer_duty.safe_get();
    //     var block_slashing_db := f_update_block_slashing_db(process.block_slashing_db, decided_beacon_block);
    //     assert process.block_slashing_db <= block_slashing_db;
    //     assert inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_ces(
    //                         process.block_consensus_engine_state, 
    //                         process.block_slashing_db); 

    //     forall s: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> |
    //                         ( && s  in process.block_consensus_engine_state.block_slashing_db_hist.Keys
    //                         && vp in process.block_consensus_engine_state.block_slashing_db_hist[s]
    //                         && db in process.block_consensus_engine_state.block_slashing_db_hist[s][vp]
    //                         )   
    //     ensures db <= block_slashing_db               
    //     {
    //         calc {
    //             db; 
    //             <=
    //             process.block_slashing_db;
    //             <=
    //             block_slashing_db;
    //         }                        
    //     }

    //     assert inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_ces(process.block_consensus_engine_state, 
    //                         block_slashing_db);
    // }

    // lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_block_consensus_decided(
    //     process: DVCState,
    //     id: Slot,
    //     decided_beacon_block: BeaconBlock, 
    //     process': DVCState
    // )
    // requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    // requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state         
    // requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    // requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process)
    // ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process')
    // {
    //     if  is_decided_data_for_current_slot(process, decided_beacon_block, id)
    //     {
    //         var new_block_slashing_db := f_update_block_slashing_db(process.block_slashing_db, decided_beacon_block);
           
    //         var block_with_signature_share := f_calc_block_with_sign_share_from_decided_block(
    //                                                     process,
    //                                                     id,
    //                                                     decided_beacon_block
    //                                                 );    

    //         var new_block_consensus_engine_state := updateConsensusInstanceValidityCheck(
    //                                                             process.block_consensus_engine_state,
    //                                                             new_block_slashing_db
    //                                                     );
            
    //         lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_ces_f_block_consensus_decided(
    //                 process,
    //                 id,
    //                 decided_beacon_block
    //             );

    //         lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_updateConsensusInstanceValidityCheck(
    //                                 process.block_consensus_engine_state,
    //                                 new_block_slashing_db,
    //                                 new_block_consensus_engine_state
    //                                 );
    //     }   
    //     else
    //     {
    //     }  
    // }

    // lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_terminate_current_proposer_duty(
    //     process: DVCState,
    //     process': DVCState
    // )
    // requires f_terminate_current_proposer_duty.requires(process)
    // requires process' == f_terminate_current_proposer_duty(process)
    // requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process)
    // ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process')
    // { }

    // lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_serve_proposer_duty(
    //     process: DVCState,
    //     proposer_duty: ProposerDuty,
    //     process': DVCState
    // )  
    // requires f_serve_proposer_duty.requires(process, proposer_duty)
    // requires process' == f_serve_proposer_duty(process, proposer_duty).state
    // requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    // requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process)
    // ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process')
    // {
    //     var process_rcvd_duty := 
    //             process.(all_rcvd_duties := process.all_rcvd_duties + {proposer_duty});
    //     var process_after_stopping_active_consensus_instance := f_terminate_current_proposer_duty(process_rcvd_duty);
    //     lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_terminate_current_proposer_duty(
    //         process_rcvd_duty,
    //         process_after_stopping_active_consensus_instance
    //     );
    //     lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_check_for_next_duty(
    //         process_after_stopping_active_consensus_instance,
    //         proposer_duty,
    //         process'
    //     );   
    // }

    // lemma lem_inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_f_listen_for_new_imported_blocks(
    //     process: DVCState,
    //     block: BeaconBlock,
    //     process': DVCState
    // )
    // requires f_listen_for_new_imported_blocks.requires(process, block)
    // requires process' == f_listen_for_new_imported_blocks(process, block).state        
    // requires inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process)
    // requires inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process)
    // ensures inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process')
    // {
    //     var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

    //     var block_consensus_instances_already_decided := process.future_consensus_instances_on_blocks_already_decided + new_consensus_instances_already_decided;

    //     var future_consensus_instances_on_blocks_already_decided := 
    //         f_listen_for_new_imported_blocks_helper_2(process, block_consensus_instances_already_decided);

    //     var process_after_stopping_consensus_instance :=
    //             process.(
    //                 future_consensus_instances_on_blocks_already_decided := future_consensus_instances_on_blocks_already_decided,
    //                 block_consensus_engine_state := stopConsensusInstances(
    //                                 process.block_consensus_engine_state,
    //                                 block_consensus_instances_already_decided.Keys
    //                 ),
    //                 block_shares_to_broadcast := process.block_shares_to_broadcast - block_consensus_instances_already_decided.Keys,
    //                 rcvd_block_shares := process.rcvd_block_shares - block_consensus_instances_already_decided.Keys                    
    //             );               
        
    //     assert inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(process);
    //     assert inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process);

    //     if pred_listen_for_new_imported_blocks_checker(process_after_stopping_consensus_instance, block_consensus_instances_already_decided)
    //     {
    //         var decided_beacon_block := block_consensus_instances_already_decided[process_after_stopping_consensus_instance.current_proposer_duty.safe_get().slot];
    //         var new_block_slashing_db := f_update_block_slashing_db(process_after_stopping_consensus_instance.block_slashing_db, decided_beacon_block);

    //         assert process_after_stopping_consensus_instance.block_slashing_db <= new_block_slashing_db;
    //         assert inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_ces(process_after_stopping_consensus_instance.block_consensus_engine_state, 
    //                           process.block_slashing_db); 

    //         forall s: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> |
    //                         ( && s  in process_after_stopping_consensus_instance.block_consensus_engine_state.block_slashing_db_hist.Keys
    //                           && vp in process_after_stopping_consensus_instance.block_consensus_engine_state.block_slashing_db_hist[s]
    //                           && db in process_after_stopping_consensus_instance.block_consensus_engine_state.block_slashing_db_hist[s][vp]
    //                         )   
    //         ensures db <= new_block_slashing_db               
    //         {
    //             calc {
    //                 db; 
    //                 <=
    //                 process_after_stopping_consensus_instance.block_slashing_db;
    //                 <=
    //                 new_block_slashing_db;
    //             }                        
    //         }
    //     }
    //     else
    //     {               
    //         assert inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(process);
    //     }
    // }   
    
    

    lemma lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body_f_add_block_to_bn(
        s: DVCState,
        block: BeaconBlock,
        s': DVCState 
    )
    requires f_add_block_to_bn.requires(s, block)
    requires s' == f_add_block_to_bn(s, block)    
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(s)
    ensures inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(s')
    { }

    lemma lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)
    ensures inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process')
    { }

    lemma lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)
    ensures inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process')
    { }      

    lemma lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)
    ensures inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process')
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
            lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)
    ensures inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process')
    { }

    lemma lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)
    ensures inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process')
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

        lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)
    ensures inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        
        lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)
    ensures inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process')
    { }  

    lemma lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)
    ensures inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process')
    { }

    lemma lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)
    ensures inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process')
    { }  

    lemma lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)
    ensures inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process')
    { }  

    lemma lem_inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)
    ensures inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process')
    { } 

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
    { }

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
    { }

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
    { }      

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
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
            lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
    { }

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
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

        lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        
        lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
    { }  

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
    { }

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
    { }  

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
    { }  

    lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(process')
    { }  

    // lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_serve_attestation_duty(
    //     process: DVCState,
    //     attestation_duty: ProposerDuty,
    //     s': DVCState,
    //     dv: DVState,
    //     n: BLSPubkey
    // )
    // requires f_serve_attestation_duty.requires(process, attestation_duty)
    // requires s' == f_serve_attestation_duty(process, attestation_duty).state   
    // requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(dv, n, process)
    // ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(dv, n, s');
    // {
    // }   

    // lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_listen_for_new_imported_blocks(
    //     process: DVCState,
    //     block: BeaconBlock,
    //     s': DVCState,
    //     dv': DVState,
    //     n: BLSPubkey,
    //     index_next_attestation_duty_to_be_served: nat        
    // )
    // requires f_listen_for_new_imported_blocks.requires(process, block)
    // requires s' == f_listen_for_new_imported_blocks(process, block).state       
    // requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(dv', n, process)
    // requires inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(dv')
    // requires inv_blocks_of_in_transit_block_shares_are_decided_values(dv')
    // requires valid_attestations_in_beacon_block(dv', process, block)
    // ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(dv', n, s');
    // {
    //     var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

    //     var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

    //     var new_process := f_stopConsensusInstances_after_receiving_new_imported_blocks(
    //                             process,
    //                             block
    //                         );   

    //     lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body_f_listen_for_new_imported_blocks_helper(
    //         dv',
    //         process,
    //         block,
    //         new_consensus_instances_already_decided
    //     );                                        
    // }         

    // lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_block_consensus_decided(
    //     process: DVCState,
    //     id: Slot,
    //     decided_attestation_data: BeaconBlock,        
    //     s': DVCState,
    //     dv: DVState,
    //     n: BLSPubkey,
    //     index_next_attestation_duty_to_be_served: nat        
    // )
    // requires f_block_consensus_decided.requires(process, id, decided_attestation_data)
    // requires s' == f_block_consensus_decided(process, id, decided_attestation_data).state
    // requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(dv, n, process)
    // ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(dv, n, s'); 
    // {

    // }           

    // lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_body_f_check_for_next_duty(
    //     process: DVCState,
    //     attestation_duty: ProposerDuty,
    //     s': DVCState,
    //     dv: DVState,
    //     n: BLSPubkey
    // )
    // requires f_check_for_next_duty.requires(process, attestation_duty)
    // requires s' == f_check_for_next_duty(process, attestation_duty).state  
    // requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(dv, n, process)
    // ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(dv, n, s')
    // {
        
    // }  

    // lemma lem_inv_slots_in_future_decided_beacon_blocks_are_correct_transpose(
    //     s: DVState,
    //     event: DV_Block_Proposer_Spec.BlockEvent,
    //     s': DVState,
    //     s_node: DVCState,
    //     n: BLSPubkey
    // )
    // requires NextEventPreCond(s, event)
    // requires NextEvent(s, event, s')      
    // requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(s, n, s_node)
    // ensures inv_slots_in_future_decided_beacon_blocks_are_correct_body(s', n, s_node)    
    // {
        
    // }   

    
    // lemma lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_f_add_block_to_bn(
    //     process: DVCState,
    //     block: BeaconBlock,
    //     process': DVCState,
    //     hn: BLSPubkey,
    //     sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
    //     index_next_proposer_duty_to_be_served: nat        
    // )
    // requires f_add_block_to_bn.requires(process, block)
    // requires process' == f_add_block_to_bn(process, block)    
    // requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(
    //                 hn, 
    //                 process, 
    //                 sequence_proposer_duties_to_be_served, 
    //                 index_next_proposer_duty_to_be_served)
    // ensures inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(
    //                 hn, 
    //                 process', 
    //                 sequence_proposer_duties_to_be_served, 
    //                 index_next_proposer_duty_to_be_served)
    // {
        
    // }
    
    // lemma lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_f_listen_for_block_signature_shares(
    //     process: DVCState,
    //     block_share: SignedBeaconBlock,
    //     process': DVCState,
    //     hn: BLSPubkey,
    //     sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
    //     index_next_proposer_duty_to_be_served: nat        
    // )
    // requires f_listen_for_block_signature_shares.requires(process, block_share)
    // requires process' == f_listen_for_block_signature_shares(process, block_share).state        
    // requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(
    //                 hn, 
    //                 process, 
    //                 sequence_proposer_duties_to_be_served, 
    //                 index_next_proposer_duty_to_be_served)
    // ensures inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(
    //                 hn, 
    //                 process', 
    //                 sequence_proposer_duties_to_be_served, 
    //                 index_next_proposer_duty_to_be_served)
    // {}

    // lemma lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_f_resend_block_share(
    //     process: DVCState,
    //     process': DVCState,
    //     hn: BLSPubkey,
    //     sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
    //     index_next_proposer_duty_to_be_served: nat  
    // )
    // requires f_resend_block_share.requires(process)
    // requires process' == f_resend_block_share(process).state        
    // requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(
    //                 hn, 
    //                 process, 
    //                 sequence_proposer_duties_to_be_served, 
    //                 index_next_proposer_duty_to_be_served)
    // ensures inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(
    //                 hn, 
    //                 process', 
    //                 sequence_proposer_duties_to_be_served, 
    //                 index_next_proposer_duty_to_be_served)
    // { } 

    // lemma lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_f_start_consensus_if_can_construct_randao_share(
    //     process: DVCState, 
    //     proposer_duty: ProposerDuty, 
    //     process': DVCState,
    //     hn: BLSPubkey,
    //     sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
    //     index_next_proposer_duty_to_be_served: nat         
    // )
    // requires f_start_consensus_if_can_construct_randao_share.requires(process)
    // requires process' == f_start_consensus_if_can_construct_randao_share(process).state       
    // requires pred_proposer_duty_is_from_dv_seq_of_proposer_duties_body(  
    //                 proposer_duty,
    //                 hn,
    //                 sequence_proposer_duties_to_be_served,    
    //                 index_next_proposer_duty_to_be_served
    //             )       
    // requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(
    //                 hn, 
    //                 process, 
    //                 sequence_proposer_duties_to_be_served, 
    //                 index_next_proposer_duty_to_be_served)
    // ensures inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(
    //                 hn, 
    //                 process', 
    //                 sequence_proposer_duties_to_be_served, 
    //                 index_next_proposer_duty_to_be_served)
    // { } 


    // lemma lem_inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_f_serve_proposer_duty(
    //     process: DVCState,
    //     proposer_duty: ProposerDuty,
    //     process': DVCState,
    //     hn: BLSPubkey,
    //     sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
    //     index_next_proposer_duty_to_be_served: nat  
    // )  
    // requires f_serve_proposer_duty.requires(process, proposer_duty)
    // requires process' == f_serve_proposer_duty(process, proposer_duty).state
    // requires && sequence_proposer_duties_to_be_served[index_next_proposer_duty_to_be_served].proposer_duty
    //                 == proposer_duty
    //          && sequence_proposer_duties_to_be_served[index_next_proposer_duty_to_be_served].node
    //                 == hn
    // requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(
    //                 hn, 
    //                 process, 
    //                 sequence_proposer_duties_to_be_served, 
    //                 index_next_proposer_duty_to_be_served)
    // ensures inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(
    //                 hn, 
    //                 process', 
    //                 sequence_proposer_duties_to_be_served, 
    //                 index_next_proposer_duty_to_be_served + 1)
    // {
    //     assert pred_proposer_duty_is_from_dv_seq_of_proposer_duties_body(  
    //                     proposer_duty,
    //                     hn,
    //                     sequence_proposer_duties_to_be_served, 
    //                     index_next_proposer_duty_to_be_served + 1
    //                 );     
    // } 

    // lemma lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_f_check_for_next_duty(
    //     process: DVCState,
    //     process': DVCState,
    //     proposer_duty: ProposerDuty,
    //     hn: BLSPubkey,
    //     sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
    //     index_next_proposer_duty_to_be_served: nat
    // )
    // requires f_check_for_next_duty.requires(process, proposer_duty)
    // requires process' == f_check_for_next_duty(process, proposer_duty).state    
    // requires pred_proposer_duty_is_from_dv_seq_of_proposer_duties_body(  
    //                     proposer_duty,
    //                     hn,
    //                     sequence_proposer_duties_to_be_served, 
    //                     index_next_proposer_duty_to_be_served
    //                 )
    // requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(
    //                 hn, 
    //                 process, 
    //                 sequence_proposer_duties_to_be_served, 
    //                 index_next_proposer_duty_to_be_served
    //          )
    // ensures inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(
    //                 hn, 
    //                 process', 
    //                 sequence_proposer_duties_to_be_served, 
    //                 index_next_proposer_duty_to_be_served)
    // {
    //     if proposer_duty.slot in process.future_consensus_instances_on_blocks_already_decided.Keys 
    //     {
    //     }
    //     else
    //     {
    //         lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_f_start_consensus_if_can_construct_randao_share(
    //             process, 
    //             proposer_duty, 
    //             process',
    //             hn,
    //             sequence_proposer_duties_to_be_served,    
    //             index_next_proposer_duty_to_be_served    
    //         );
    //     }   
    // }

    // lemma lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_f_block_consensus_decided(
    //     process: DVCState,
    //     id: Slot,
    //     decided_beacon_block: BeaconBlock, 
    //     process': DVCState,
    //     hn: BLSPubkey,
    //     sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
    //     index_next_proposer_duty_to_be_served: nat
    // )
    // requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    // requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state         
    // requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(
    //                 hn, 
    //                 process, 
    //                 sequence_proposer_duties_to_be_served, 
    //                 index_next_proposer_duty_to_be_served
    //          )
    // ensures inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(
    //                 hn, 
    //                 process', 
    //                 sequence_proposer_duties_to_be_served, 
    //                 index_next_proposer_duty_to_be_served)
    // { } 

    // lemma lem_inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_f_listen_for_new_imported_blocks(
    //     process: DVCState,
    //     block: BeaconBlock,
    //     process': DVCState,
    //     hn: BLSPubkey,
    //     sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
    //     index_next_proposer_duty_to_be_served: nat
    // )
    // requires f_listen_for_new_imported_blocks.requires(process, block)
    // requires process' == f_listen_for_new_imported_blocks(process, block).state        
    // requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(
    //                 hn, 
    //                 process, 
    //                 sequence_proposer_duties_to_be_served, 
    //                 index_next_proposer_duty_to_be_served
    //          )
    // ensures inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(
    //                 hn, 
    //                 process', 
    //                 sequence_proposer_duties_to_be_served, 
    //                 index_next_proposer_duty_to_be_served)
    // { } 

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_f_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process, 
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process',
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    { }

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process, 
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process',
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    { }

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process, 
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process',
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)  
    { } 

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process, 
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process',
                hn, 
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
            lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
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

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process, 
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process',
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)  
    { } 

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process, 
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process',
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)  
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

        lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process', 
            hn,
            sequence_proposer_duties_to_be_served, 
            index_next_proposer_duty_to_be_served
        );
    }

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_helper( 
                proposer_duty,
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served
            )
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process, 
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process',
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)  
    { 
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);

        lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty, 
            hn, 
            sequence_proposer_duties_to_be_served, 
            index_next_proposer_duty_to_be_served
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);

        forall duty: ProposerDuty | duty in process_after_receiving_duty.all_rcvd_duties
        ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_helper(        
                    duty,
                    hn, 
                    sequence_proposer_duties_to_be_served,    
                    index_next_proposer_duty_to_be_served
                )
        {
            if duty in process_after_stopping_current_duty.all_rcvd_duties
            {
                assert inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_helper(        
                    duty,
                    hn, 
                    sequence_proposer_duties_to_be_served,    
                    index_next_proposer_duty_to_be_served
                );
            }
            else
            {
                assert duty == proposer_duty;
                assert inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_helper(        
                    duty,
                    hn, 
                    sequence_proposer_duties_to_be_served,    
                    index_next_proposer_duty_to_be_served
                );
            }
        }

        assert  inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                    process_after_receiving_duty, 
                    hn, 
                    sequence_proposer_duties_to_be_served, 
                    index_next_proposer_duty_to_be_served
                );

        lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process', 
            hn, 
            sequence_proposer_duties_to_be_served, 
            index_next_proposer_duty_to_be_served
        );
    }

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock, 
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state 
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process, 
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process',
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)  
    { }  


    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process, 
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process',
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)  
    {}

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process, 
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process',
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)  
    { }   

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat  
    )
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process, 
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                process',
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)  
    { } 

    lemma lem_inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_f_resend_block_share(
        s: DVCState,
        s': DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat  
    )
    requires f_resend_block_share.requires(s)
    requires s' == f_resend_block_share(s).state
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                s, 
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)
    ensures inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                s',
                hn, 
                sequence_proposer_duties_to_be_served, 
                index_next_proposer_duty_to_be_served)  
    { } 

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    { }

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    { }

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    { }      

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
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
            lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires && process.latest_proposer_duty.isPresent()
             && process.all_rcvd_duties != {}
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    { }

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.all_rcvd_duties != {}
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
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

        lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        
        lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );
    } 

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    { }  

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    { }

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    { }  

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    { }  

    lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    { }  

    // lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_start_consensus_if_can_construct_randao_share(
    //     process: DVCState,
    //     proposer_duty: ProposerDuty,
    //     process': DVCState
    // )  
    // requires f_start_consensus_if_can_construct_randao_share.requires(process)
    // requires process' == f_start_consensus_if_can_construct_randao_share(process).state
    // requires process.all_rcvd_duties != {}
    // ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    // { }

    // lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_check_for_next_duty(
    //     process: DVCState,
    //     proposer_duty: ProposerDuty,
    //     process': DVCState
    // )  
    // requires f_check_for_next_duty.requires(process, proposer_duty)
    // requires process' == f_check_for_next_duty(process, proposer_duty).state
    // requires process.all_rcvd_duties != {}
    // ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    // { 
    //     if proposer_duty.slot in process.future_consensus_instances_on_blocks_already_decided.Keys
    //     {
    //         assert inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process');
    //     } 
    //     else
    //     {
    //         lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_start_consensus_if_can_construct_randao_share(
    //             process,
    //             proposer_duty,
    //             process'
    //         );
    //         assert inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process');
    //     }
    // }

    // lemma lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_serve_proposer_duty(
    //     process: DVCState,
    //     proposer_duty: ProposerDuty,
    //     process': DVCState
    // )  
    // requires f_serve_proposer_duty.requires(process, proposer_duty)
    // requires process' == f_serve_proposer_duty(process, proposer_duty).state
    // requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    // ensures inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process')
    // { 
    //     var process_rcvd_duty := 
    //             process.(all_rcvd_duties := process.all_rcvd_duties + {proposer_duty});
    //     assert process_rcvd_duty.all_rcvd_duties != {};
    //     var process_after_stopping_active_consensus_instance := f_terminate_current_proposer_duty(process_rcvd_duty);
    //     assert process_after_stopping_active_consensus_instance.all_rcvd_duties != {};
    //     lem_inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body_f_check_for_next_duty(
    //         process_after_stopping_active_consensus_instance,
    //         proposer_duty,
    //         process'
    //     );  
    // }

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
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

        assert inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process_after_adding_randao_share);

        lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    requires inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(process)
    requires inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_proposer_duties_body(process, proposer_duty)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
    { 
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        
        lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        assert inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process_after_stopping_current_duty);

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);

        assert inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process_after_receiving_duty);
       
        lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
    { } 

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
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
            lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    } 

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process)
    ensures inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(process')
    { } 

    // lemma lem_inv_one_honest_process_is_required_to_pass_signer_threshold(
    //     dv: DVState,
    //     block_shares: set<SignedBeaconBlock>,
    //     signing_root: Root
    // )
    // requires signer_threshold(dv.all_nodes, block_shares, signing_root)
    // requires inv_all_honest_nodes_is_a_quorum(dv)
    // ensures && var signers := 
    //                 set signer, block_share | 
    //                     && block_share in block_shares
    //                     && signer in dv.all_nodes
    //                     && verify_bls_signature(signing_root, block_share.signature, signer)
    //                 ::
    //                     signer;
    //         && exists hn :: hn in signers && is_an_honest_node(dv, hn)
    // {   
    //     var all_nodes := dv.all_nodes;
    //     var byz := dv.adversary.nodes;
    //     var signers := 
    //                 set signer, block_share | 
    //                     && block_share in block_shares
    //                     && signer in all_nodes
    //                     && verify_bls_signature(signing_root, block_share.signature, signer)
    //                 ::
    //                     signer;

    //     assert |signers| >= quorum(|all_nodes|);
    //     assert signers <= all_nodes;
    //     assert |byz| <= f(|all_nodes|);

    //     lemmaThereExistsAnHonestInQuorum(all_nodes, byz, signers);
    // }  

    // lemma lem_f_construct_aggregated_block_for_new_block_share_construct_valid_blocks(
    //     construct_signed_block_signature: (set<SignedBeaconBlock>) -> Optional<BLSSignature>,
    //     dv_pubkey: BLSPubkey,
    //     all_nodes: set<BLSPubkey>, 
    //     block: Block,
    //     block_share: SignedBeaconBlock, 
    //     k: (BeaconBlock, seq<bool>),
    //     rcvd_block_shares: map<Slot,map<(BeaconBlock, seq<bool>), set<SignedBeaconBlock>>>
    // )
    // requires construct_complete_signed_block_assumptions_reverse(
    //             construct_signed_block_signature,
    //             dv_pubkey,
    //             all_nodes
    //          )
    // requires block_share.block.slot in rcvd_block_shares.Keys
    // requires k in rcvd_block_shares[block_share.block.slot]
    // requires construct_signed_block_signature(rcvd_block_shares[block_share.block.slot][k]).isPresent()    
    // requires signed_beacon_blocks_for_the_same_beacon_block(rcvd_block_shares[block_share.block.slot][k], block.data)
    // requires && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(block.data.target.epoch));
    //          && var block_signing_root := compute_block_signing_root(block.data, fork_version);      
    //          && signer_threshold(all_nodes, rcvd_block_shares[block_share.block.slot][k], block_signing_root) 
    // requires block 
    //          == 
    //          f_construct_aggregated_block_for_new_block_share(
    //                         block_share,
    //                         k, 
    //                         construct_signed_block_signature,
    //                         rcvd_block_shares
    //                     );
    // ensures is_verified_block_with_pubkey(block, dv_pubkey)
    // {
        
    // }

    lemma lem_inv_submitted_outputs_blocks_are_valid_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState
    )
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    ensures inv_submitted_outputs_blocks_are_valid(
                f_start_consensus_if_can_construct_randao_share(process).outputs,
                process'.dv_pubkey
                )
    { }  

    lemma lem_inv_submitted_outputs_blocks_are_valid_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState
    )
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    ensures inv_submitted_outputs_blocks_are_valid(
                f_listen_for_randao_shares(process, randao_share).outputs,
                process'.dv_pubkey
            )
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
            lem_inv_submitted_outputs_blocks_are_valid_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }    

    lemma lem_inv_submitted_outputs_blocks_are_valid_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    ensures inv_submitted_outputs_blocks_are_valid(
                f_check_for_next_duty(process, proposer_duty).outputs,
                process'.dv_pubkey
            )
    { }

    lemma lem_inv_submitted_outputs_blocks_are_valid_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
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

        lem_inv_submitted_outputs_blocks_are_valid_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_submitted_outputs_blocks_are_valid_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    ensures inv_submitted_outputs_blocks_are_valid(
                f_serve_proposer_duty(process, proposer_duty).outputs,
                process'.dv_pubkey
            )
    {
        var process_after_stopping_current_duty := 
            f_terminate_current_proposer_duty(process);

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);

        lem_inv_submitted_outputs_blocks_are_valid_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_submitted_outputs_blocks_are_valid_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state 
    ensures inv_submitted_outputs_blocks_are_valid(
                f_block_consensus_decided(process, id, decided_beacon_block).outputs,
                process'.dv_pubkey
            )
    { }  

    lemma lem_inv_submitted_outputs_blocks_are_valid_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires construct_complete_signed_block_assumptions_reverse(
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
            if process.construct_complete_signed_block(process_with_new_block_share.rcvd_block_shares[slot][data]).isPresent() 
            {                
                    var complete_signed_block := process.construct_complete_signed_block(process_with_new_block_share.rcvd_block_shares[slot][data]).safe_get();                      

                    rs_block_sign_and_verification_propeties();
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
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    ensures inv_submitted_outputs_blocks_are_valid(
                f_listen_for_new_imported_blocks(process, block).outputs,
                process'.dv_pubkey
            )
    { }  

    lemma lem_inv_submitted_outputs_blocks_are_valid_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    ensures inv_submitted_outputs_blocks_are_valid(
                f_resend_randao_share(process).outputs,
                process'.dv_pubkey
            )
    { }  

    lemma lem_inv_submitted_outputs_blocks_are_valid_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    ensures inv_submitted_outputs_blocks_are_valid(
                f_resend_block_share(process).outputs,
                process'.dv_pubkey
            )
    { }  

    lemma lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    ensures && var outputs := f_start_consensus_if_can_construct_randao_share(process).outputs;
            && inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(outputs, process')
    { }  

    lemma lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    ensures && var outputs := f_listen_for_randao_shares(process, randao_share).outputs;
            && inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(outputs, process')
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
            lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    } 
        
    lemma lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    ensures && var outputs := f_resend_randao_share(process).outputs;
            && inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(outputs, process')
    { }  

    lemma lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_resend_block_share(
        process: DVCState,
        process': DVCState
    )
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures && var outputs := f_resend_block_share(process).outputs;
            && inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(outputs, process')
    {
        var new_outputs := getEmptyOuputs().(
                                    sent_block_shares :=
                                        multicast_multiple(process.block_shares_to_broadcast.Values, process.peers)
                                );

    }  

    lemma lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    ensures && var outputs := f_check_for_next_duty(process, proposer_duty).outputs;
            && inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(outputs, process')
    { }

    lemma lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    ensures && var outputs := f_broadcast_randao_share(process, proposer_duty).outputs;
            && inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(outputs, process')
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

        lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    ensures && var outputs := f_serve_proposer_duty(process, proposer_duty).outputs;
            && inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(outputs, process')
    {
        var process_after_stopping_current_duty := 
            f_terminate_current_proposer_duty(process);

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
        
        
        lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock, 
        process': DVCState
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
            var fork_version := bn_get_fork_version(decided_beacon_block.slot);
            var block_signature := rs_sign_block(decided_beacon_block, fork_version, block_signing_root, process.rs);
            var block_share := SignedBeaconBlock(decided_beacon_block, block_signature);

            rs_block_sign_and_verification_propeties( );
            assert  verify_bls_signature(
                        block_signing_root, 
                        block_share.signature, 
                        process.rs.pubkey
                    );

            var outputs := f_block_consensus_decided(process, id, decided_beacon_block).outputs;

            forall block_share: SignedBeaconBlock | block_share in getMessagesFromMessagesWithRecipient(outputs.sent_block_shares) 
            assert inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_body(process', block_share);
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
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    ensures && var outputs := f_listen_for_block_signature_shares(process, block_share).outputs;
            && inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(outputs, process')
    { }

    lemma lem_inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    ensures && var outputs := f_listen_for_new_imported_blocks(process, block).outputs;
            && inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(outputs, process')
    { }  

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
    { }

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
    { }

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
    { }      

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
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
            lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
    { }

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
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

        lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        
        lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        ); 
    } 

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock, 
        process': DVCState
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
            var fork_version := bn_get_fork_version(decided_beacon_block.slot);
            var block_signature := rs_sign_block(decided_beacon_block, fork_version, block_signing_root, process.rs);
            var new_block_share := SignedBeaconBlock(decided_beacon_block, block_signature);

            rs_block_sign_and_verification_propeties();           
            assert verify_bls_signature(block_signing_root, new_block_share.signature, process.rs.pubkey);
            assert pred_is_the_owner_of_a_block_share(process.rs.pubkey, new_block_share);            
        }     
        else 
        {
            var outputs := f_block_consensus_decided(process, id, decided_beacon_block).outputs;
            assert inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process');
        }
    } 

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
    { }

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
    { }  

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
    { }  

    lemma lem_inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process)
    ensures inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(process')
    { }  

    lemma lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState
    )
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    ensures inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum(                
                f_start_consensus_if_can_construct_randao_share(process).outputs,
                process'
            )
    { }  

    lemma lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    ensures inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum(
                f_check_for_next_duty(process, proposer_duty).outputs,
                process'
            )
    { }

    lemma lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    ensures inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum(
                f_broadcast_randao_share(process, proposer_duty).outputs,
                process'
            )
    { }

    lemma lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    ensures inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum(
                f_serve_proposer_duty(process, proposer_duty).outputs,
                process'
            )
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);


        lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum_f_listen_for_randao_shares(
        process: DVCState,
        randao_share: RandaoShare,
        process': DVCState
    )
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state
    ensures inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum(
                f_listen_for_randao_shares(process, randao_share).outputs,
                process'
            )
    { }  

    lemma lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    ensures inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum(
                f_listen_for_new_imported_blocks(process, block).outputs,
                process'
            )
    { }  

    lemma lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires construct_complete_signed_block_assumptions_reverse(
                process.construct_complete_signed_block,
                process.dv_pubkey,
                process.peers
             )
    ensures inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum(
                f_listen_for_block_signature_shares(process, block_share).outputs,
                process'
                )
    { 
        var slot := block_share.block.slot;

        if is_slot_for_current_or_future_instances(process, slot)
        {
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
                        
            if process.construct_complete_signed_block(process_with_new_block_share.rcvd_block_shares[slot][data]).isPresent() 
            {
                assert  inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum(
                            f_listen_for_block_signature_shares(process, block_share).outputs,
                            process'
                        );            
            }
            else 
            {
                assert  inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum(
                            f_listen_for_block_signature_shares(process, block_share).outputs,
                            process'
                        );
            }
        }            
        else 
        {
            assert  inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum(
                        f_listen_for_block_signature_shares(process, block_share).outputs,
                        process'
                    );
        }
            
    }

    lemma lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state 
    ensures inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum(
                f_block_consensus_decided(process, id, decided_beacon_block).outputs,
                process'
            )
    { }  

    lemma lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    ensures inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum(
                f_resend_randao_share(process).outputs,
                process'
            )
    { }  

    lemma lem_inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    ensures inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum(
                f_resend_block_share(process).outputs,
                process'
            )
    { } 

    lemma lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
    { }

    lemma lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_terminate_current_proposer_duty(        
        process: DVCState, 
        process': DVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
    { } 

    lemma lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_start_consensus_if_can_construct_randao_share(        
        process: DVCState, 
        process': DVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state   
    requires (  forall block_share: SignedBeaconBlock |
                    && block_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
                    ::
                    && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process, block_share)             
            )
    requires inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
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
               && proposer_duty.slot !in process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys 
            {
                var rs_pubkey: BLSPubkey := process.rs.pubkey;
                assert rs_pubkey == process'.rs.pubkey;

                var duty_slot := proposer_duty.slot;
                var block_slashing_db := process.block_slashing_db;
                var block_slashing_db' := process'.block_slashing_db;
                assert block_slashing_db == block_slashing_db';
                assert  (  forall block_share: SignedBeaconBlock |
                            && block_share in allMessagesSent 
                            && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
                            ::
                            && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process', block_share)             
                        );

                var block_slashing_db_hist: map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>> 
                    := process.block_consensus_engine_state.block_slashing_db_hist;        
                var block_slashing_db_hist': map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>> 
                    := process'.block_consensus_engine_state.block_slashing_db_hist;
                    
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
                var new_active_consensus_instances_on_beacon_blocks := 
                    process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[
                        duty_slot := bcvc
                    ];              

                assert  block_slashing_db_hist' == 
                        addToBlockSlashingDBHist(
                            block_slashing_db_hist,
                            duty_slot,
                            bcvc.validityPredicate,
                            block_slashing_db                    
                        );

                forall slot: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> | 
                    && slot in block_slashing_db_hist'.Keys
                    && vp in block_slashing_db_hist'[slot].Keys
                    && db in block_slashing_db_hist'[slot][vp]
                ensures inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(            
                                allMessagesSent,
                                process'.rs.pubkey,
                                slot,
                                vp,
                                db
                            );   
                {
                    if slot != duty_slot || vp != new_vp
                    {
                        assert inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(            
                            allMessagesSent,
                            process.rs.pubkey,
                            slot,
                            vp,
                            db
                        );                
                    }
                    else
                    {
                        var hist_slot := getOrDefault(block_slashing_db_hist, slot, map[]);
                        var hist_slot_vp := getOrDefault(hist_slot, vp, {});
                        var new_hist_slot := getOrDefault(block_slashing_db_hist', slot, map[]);
                        var new_hist_slot_vp := getOrDefault(new_hist_slot, vp, {});

                        assert  block_slashing_db_hist' == 
                                addToBlockSlashingDBHist(
                                    block_slashing_db_hist,
                                    slot,
                                    bcvc.validityPredicate,
                                    block_slashing_db                    
                                );
                        
                        assert hist_slot_vp + {block_slashing_db} == new_hist_slot_vp;

                        if db in hist_slot_vp
                        {                    
                            assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(            
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
                                        && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
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
                assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                            allMessagesSent,
                            process'
                        );
            }
        }
        else
        {
            assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                            allMessagesSent,
                            process'
                    );
        }        
    }  

    lemma lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires (  forall block_share: SignedBeaconBlock |
                    && block_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
                    ::
                    && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process, block_share)             
            )
    requires inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
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

            var rs_pubkey: BLSPubkey := process.rs.pubkey;
            assert rs_pubkey == process_with_new_randao_share.rs.pubkey;

            lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process',
                allMessagesSent
            );
        }
        else
        { }
    } 

    lemma lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_updateBlockSlashingDBHist(
        hist: map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>>,
        new_active_consensus_instances_on_beacon_blocks : map<Slot, BlockConsensusValidityCheckState>,
        new_block_slashing_db: set<SlashingDBBlock>,
        new_hist: map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>>,
        allMessagesSent: set<SignedBeaconBlock>,
        rs_pubkey: BLSPubkey
    )    
    requires new_hist == updateBlockSlashingDBHist(hist, new_active_consensus_instances_on_beacon_blocks, new_block_slashing_db)
    requires (  forall slot: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> | 
                        && slot in hist
                        && vp in hist[slot]
                        && db in hist[slot][vp]
                        :: 
                        inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(
                            allMessagesSent,
                            rs_pubkey,
                            slot,
                            vp,
                            db
                        )
    )
    requires (  forall block_share: SignedBeaconBlock | 
                        && block_share in allMessagesSent 
                        && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
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
                    && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
                    && block_share.block.slot < slot             
                    ::
                    inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(
                        allMessagesSent,
                        rs_pubkey,
                        slot,
                        vp,
                        db
                    )
    )
    {
        assert hist.Keys + new_active_consensus_instances_on_beacon_blocks.Keys == new_hist.Keys;

        forall slot: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock>, block_share: SignedBeaconBlock | 
                    && slot in new_hist.Keys
                    && vp in new_hist[slot]
                    && db in new_hist[slot][vp]
                    && block_share in allMessagesSent
                    && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
                    && block_share.block.slot < slot             
        ensures inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(
                        allMessagesSent,
                        rs_pubkey,
                        slot,
                        vp,
                        db
                    )
        {
            if slot in new_active_consensus_instances_on_beacon_blocks.Keys
            {
                if slot in hist.Keys && vp in hist[slot].Keys && db in hist[slot][vp]
                {                    
                    assert inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(
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
                    assert inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(
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
                assert inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(
                            allMessagesSent,
                            rs_pubkey,
                            slot,
                            vp,
                            db
                        );
            }
        }
    }

    

    lemma lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_updateConsensusInstanceValidityCheck(
        s: BlockConsensusEngineState,
        new_block_slashing_db: set<SlashingDBBlock>,
        s': BlockConsensusEngineState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires s' == updateConsensusInstanceValidityCheck(s, new_block_slashing_db)
    {
        var new_active_consensus_instances_on_beacon_blocks := updateConsensusInstanceValidityCheckHelper(
                    s.active_consensus_instances_on_beacon_blocks,
                    new_block_slashing_db
                );

        forall slot: Slot | slot in new_active_consensus_instances_on_beacon_blocks.Keys
        ensures && var validityPredicate := new_active_consensus_instances_on_beacon_blocks[slot].validityPredicate;
                && var proposer_duty := new_active_consensus_instances_on_beacon_blocks[slot].proposer_duty;
                && var randao_reveal := new_active_consensus_instances_on_beacon_blocks[slot].randao_reveal;
                && ( forall block: BeaconBlock 
                        ::
                        validityPredicate(block)
                        <==> 
                        ci_decision_is_valid_beacon_block(new_block_slashing_db, block, proposer_duty, randao_reveal)
                )
        {
            var validityPredicate := new_active_consensus_instances_on_beacon_blocks[slot].validityPredicate;
            var proposer_duty := new_active_consensus_instances_on_beacon_blocks[slot].proposer_duty;
            var randao_reveal := new_active_consensus_instances_on_beacon_blocks[slot].randao_reveal;
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
                    active_consensus_instances_on_beacon_blocks := new_active_consensus_instances_on_beacon_blocks,
                    block_slashing_db_hist := updateBlockSlashingDBHist(
                        s.block_slashing_db_hist,
                        new_active_consensus_instances_on_beacon_blocks,
                        new_block_slashing_db
                    )
                );
    }

    lemma lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_check_for_next_duty(        
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires (  forall block_share: SignedBeaconBlock |
                    && block_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
                    ::
                    && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process, block_share)             
            )
    requires inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
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

            var new_active_consensus_instances_on_beacon_blocks := updateConsensusInstanceValidityCheckHelper(
                    process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks,
                    new_block_slashing_db
                );

            var new_process := 
                process.(
                    current_proposer_duty := None,                          
                    future_consensus_instances_on_blocks_already_decided := process.future_consensus_instances_on_blocks_already_decided - {proposer_duty.slot},
                    block_slashing_db := new_block_slashing_db,
                    block_consensus_engine_state := updateConsensusInstanceValidityCheck(
                        process.block_consensus_engine_state,
                        new_block_slashing_db
                    )                        
                );

            lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_updateBlockSlashingDBHist(
                process.block_consensus_engine_state.block_slashing_db_hist,                 
                new_active_consensus_instances_on_beacon_blocks,
                new_block_slashing_db,
                process'.block_consensus_engine_state.block_slashing_db_hist,
                allMessagesSent,
                process.rs.pubkey
            );
        }
        else
        {
            lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_start_consensus_if_can_construct_randao_share(                
                process, 
                process',
                allMessagesSent
            );
        }
    }  

    lemma lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    requires (  forall block_share: SignedBeaconBlock |
                    && block_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
                    ::
                    && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process, block_share)             
            )
    requires inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
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

        lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process',
            allMessagesSent
        );
    }

    lemma lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_serve_proposer_duty(        
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires (  forall block_share: SignedBeaconBlock |
                    && block_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
                    ::
                    && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process, block_share)             
            )
    requires inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);

        assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                                    
                    allMessagesSent,
                    process_after_stopping_current_duty                    
                );

        assert  (  forall block_share: SignedBeaconBlock |
                                && block_share in allMessagesSent 
                                && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                                && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
                                ::
                                && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process_after_stopping_current_duty, block_share)             
                );

        lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty,
            allMessagesSent
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);

        assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                                    
                    allMessagesSent,
                    process_after_receiving_duty                    
                );

        assert  (  forall block_share: SignedBeaconBlock |
                                && block_share in allMessagesSent 
                                && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                                && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
                                ::
                                && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process_after_receiving_duty, block_share)             
                );

        lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process',
            allMessagesSent
        );  
    }   

    lemma lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires (  forall block_share: SignedBeaconBlock |
                    && block_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
                    ::
                    && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process, block_share)             
            )
    requires inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
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
                    block_consensus_engine_state := stopConsensusInstances(
                                    process.block_consensus_engine_state,
                                    consensus_instances_on_blocks_already_decided.Keys
                    ),
                    block_shares_to_broadcast := process.block_shares_to_broadcast - consensus_instances_on_blocks_already_decided.Keys,
                    rcvd_block_shares := process.rcvd_block_shares - consensus_instances_on_blocks_already_decided.Keys                    
                );         

        assert inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process_after_stopping_consensus_instance
            );          
        assert (  forall block_share: SignedBeaconBlock |
                    && block_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
                    ::
                    && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process_after_stopping_consensus_instance, block_share)             
            );

        if  && process_after_stopping_consensus_instance.current_proposer_duty.isPresent() 
            && process_after_stopping_consensus_instance.current_proposer_duty.safe_get().slot in consensus_instances_on_blocks_already_decided 
        {
            var decided_beacon_block := consensus_instances_on_blocks_already_decided[process_after_stopping_consensus_instance.current_proposer_duty.safe_get().slot];
            var new_block_slashing_db := f_update_block_slashing_db(process_after_stopping_consensus_instance.block_slashing_db, decided_beacon_block);
            
            assert process_after_stopping_consensus_instance.block_slashing_db <= new_block_slashing_db;

            var new_active_consensus_instances_on_beacon_blocks := updateConsensusInstanceValidityCheckHelper(
                    process_after_stopping_consensus_instance.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks,
                    new_block_slashing_db
                );

            assert  process'.block_consensus_engine_state.block_slashing_db_hist 
                    == 
                    updateBlockSlashingDBHist(
                        process_after_stopping_consensus_instance.block_consensus_engine_state.block_slashing_db_hist, 
                        new_active_consensus_instances_on_beacon_blocks, 
                        new_block_slashing_db
                    );

            lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_updateBlockSlashingDBHist(
                process_after_stopping_consensus_instance.block_consensus_engine_state.block_slashing_db_hist,                 
                new_active_consensus_instances_on_beacon_blocks,
                new_block_slashing_db,
                process'.block_consensus_engine_state.block_slashing_db_hist,
                allMessagesSent,
                process.rs.pubkey
            );
        }
        else
        {
            assert inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            );
        }
    }  

    lemma lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_block_consensus_decided_new_sent_block_shares(        
        process: DVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock, 
        process': DVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state         
    requires (  forall block_share: SignedBeaconBlock |
                    && block_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
                    ::
                    && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process, block_share)             
            )
    requires inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    requires && process.current_proposer_duty.isPresent()
             && id == process.current_proposer_duty.safe_get().slot
             && id == decided_beacon_block.slot
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    requires ( forall slot  |
                        slot in process'.block_consensus_engine_state.block_slashing_db_hist.Keys
                        ::
                        slot <= process'.latest_proposer_duty.safe_get().slot
             )
    ensures && var outputs := f_block_consensus_decided(process, id, decided_beacon_block).outputs;
            && var allMessagesSent' := allMessagesSent + getMessagesFromMessagesWithRecipient(outputs.sent_block_shares);
            && inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                    allMessagesSent',
                    process'
                )
    ensures && var new_block_slashing_db := f_update_block_slashing_db(process.block_slashing_db, decided_beacon_block);
            && var block_signing_root := compute_block_signing_root(decided_beacon_block);
            && var fork_version := bn_get_fork_version(decided_beacon_block.slot);
            && var block_signature := rs_sign_block(decided_beacon_block, fork_version, block_signing_root, process.rs);
            && var block_share := SignedBeaconBlock(decided_beacon_block, block_signature); 
            && pred_is_the_owner_of_a_block_share(process'.rs.pubkey, block_share)
            && ( forall slot: Slot | slot in process'.block_consensus_engine_state.block_slashing_db_hist.Keys ::
                    block_share.block.slot >= slot
            )
    {
        var new_block_slashing_db := f_update_block_slashing_db(process.block_slashing_db, decided_beacon_block);
        var block_signing_root := compute_block_signing_root(decided_beacon_block);
        var fork_version := bn_get_fork_version(decided_beacon_block.slot);
        var block_signature := rs_sign_block(decided_beacon_block, fork_version, block_signing_root, process.rs);
        var block_share := SignedBeaconBlock(decided_beacon_block, block_signature);
        var slot := decided_beacon_block.slot;

        rs_block_sign_and_verification_propeties();        
        assert verify_bls_signature(
                        block_signing_root,
                        rs_sign_block(decided_beacon_block, fork_version, block_signing_root, process.rs),
                        process.rs.pubkey
                    );
        assert pred_is_the_owner_of_a_block_share(process.rs.pubkey, block_share);
        assert process'.rs.pubkey == process.rs.pubkey;
        assert pred_is_the_owner_of_a_block_share(process'.rs.pubkey, block_share);

        assert process.block_slashing_db <= new_block_slashing_db;                                                    

        assert process.latest_proposer_duty.isPresent();
        assert && process'.latest_proposer_duty.isPresent()
               && process'.latest_proposer_duty.safe_get()
                  ==
                  process.latest_proposer_duty.safe_get()  ;

        var new_active_consensus_instances_on_beacon_blocks := updateConsensusInstanceValidityCheckHelper(
                process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks,
                new_block_slashing_db
            );        

        lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_updateBlockSlashingDBHist(
            process.block_consensus_engine_state.block_slashing_db_hist,                 
            new_active_consensus_instances_on_beacon_blocks,
            new_block_slashing_db,
            process'.block_consensus_engine_state.block_slashing_db_hist,
            allMessagesSent,
            process.rs.pubkey
        );

        assert  inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(
                    allMessagesSent,
                    process'
                );
        assert process.rs.pubkey == process'.rs.pubkey;

        var allMessagesSent' := allMessagesSent + {block_share};

        forall slot: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> | 
                    && slot in process'.block_consensus_engine_state.block_slashing_db_hist.Keys
                    && vp in process'.block_consensus_engine_state.block_slashing_db_hist[slot].Keys
                    && db in process'.block_consensus_engine_state.block_slashing_db_hist[slot][vp]
        ensures inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(
                    allMessagesSent',
                    process'.rs.pubkey,
                    slot,
                    vp,
                    db
                )
        {
            var hist := process.block_consensus_engine_state.block_slashing_db_hist;
            var hist' := process'.block_consensus_engine_state.block_slashing_db_hist;            
            var hist_slot := getOrDefault(hist, slot, map[]);
            var hist_slot' := getOrDefault(hist', slot, map[]);
            var hist_slot_vp := getOrDefault(hist_slot, vp, {});
            var hist_slot_vp' := getOrDefault(hist_slot', vp, {});

            assert || hist_slot_vp' == hist_slot_vp 
                   || hist_slot_vp' == hist_slot_vp + {new_block_slashing_db};

            forall block_share: SignedBeaconBlock | 
                && block_share in allMessagesSent'
                && pred_is_the_owner_of_a_block_share(process'.rs.pubkey, block_share)
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

    lemma lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
             )    
    { }

    lemma lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock, 
        process': DVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state         
    requires (  forall block_share: SignedBeaconBlock |
                    && block_share in allMessagesSent 
                    && var rs_pubkey: BLSPubkey := process.rs.pubkey;
                    && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
                    ::
                    && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(process, block_share)             
            )
    requires inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
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
            assert inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            );
        }
            
    }

    lemma lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_resend_block_share(        
        process: DVCState,
        process': DVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state       
    requires process.block_shares_to_broadcast.Values <= allMessagesSent 
    requires inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
    { }

    lemma lem_inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_f_resend_randao_share(
        process: DVCState, 
        process': DVCState,
        allMessagesSent: set<SignedBeaconBlock>
    )
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process
             )
    ensures inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(                
                allMessagesSent,
                process'
            )
    { }  

    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    ensures process.rs.pubkey == process'.rs.pubkey
    { }
    
    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    ensures process.rs.pubkey == process'.rs.pubkey
    { }

    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    ensures process.rs.pubkey == process'.rs.pubkey
    { }   

    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    ensures process.rs.pubkey == process'.rs.pubkey
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
            lem_inv_unchanged_dvc_rs_pubkey_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }        
    }  

    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    ensures process.rs.pubkey == process'.rs.pubkey
    { }

    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    ensures process.rs.pubkey == process'.rs.pubkey
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

        lem_inv_unchanged_dvc_rs_pubkey_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    ensures process.rs.pubkey == process'.rs.pubkey
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        
        lem_inv_unchanged_dvc_rs_pubkey_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_unchanged_dvc_rs_pubkey_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );
    } 

    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    ensures process.rs.pubkey == process'.rs.pubkey
    { }  

    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    ensures process.rs.pubkey == process'.rs.pubkey
    { }

    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    ensures process.rs.pubkey == process'.rs.pubkey
    { }  

    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    ensures process.rs.pubkey == process'.rs.pubkey
    { }  

    lemma lem_inv_unchanged_dvc_rs_pubkey_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    ensures process.rs.pubkey == process'.rs.pubkey
    { }     

    lemma lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_f_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process, index_next_proposer_duty_to_be_served)
    ensures inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served)
    { }    

    lemma lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process, index_next_proposer_duty_to_be_served)
    ensures inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served)
    { }

    lemma lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_startConsensusInstance_helper(
        s: BlockConsensusEngineState,
        id: Slot,
        proposer_duty: ProposerDuty,
        block_slashing_db: set<SlashingDBBlock>,
        complete_signed_randao_reveal: BLSSignature,
        s': BlockConsensusEngineState
    )
    requires startConsensusInstance.requires(s, id, proposer_duty, block_slashing_db, complete_signed_randao_reveal)
    requires s' == startConsensusInstance(s, id, proposer_duty, block_slashing_db, complete_signed_randao_reveal)
    ensures s.block_slashing_db_hist.Keys + { proposer_duty.slot } == s'.block_slashing_db_hist.Keys
    {  }


    lemma lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState,        
        process': DVCState,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state  
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)
    requires inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process, index_next_proposer_duty_to_be_served)
    requires inv_available_current_proposer_duty_is_from_dv_seq_of_proposer_duties_body(process, n, sequence_proposer_duties_to_be_served, index_next_proposer_duty_to_be_served)
    ensures inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served)
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
               && proposer_duty.slot !in process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys 
            {
                lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_startConsensusInstance_helper(
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

    lemma lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)
    requires inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process, index_next_proposer_duty_to_be_served)
    requires inv_available_current_proposer_duty_is_from_dv_seq_of_proposer_duties_body(process, n, sequence_proposer_duties_to_be_served, index_next_proposer_duty_to_be_served)
    ensures inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served)
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
            lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process',
                sequence_proposer_duties_to_be_served,
                n,
                index_next_proposer_duty_to_be_served
            );
        }
        else
        { }
    } 

    lemma lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_updateConsensusInstanceValidityCheck_helper(
        s: BlockConsensusEngineState,
        new_block_slashing_db: set<SlashingDBBlock>,
        s': BlockConsensusEngineState
    )
    requires updateConsensusInstanceValidityCheck.requires(s, new_block_slashing_db)
    requires s' == updateConsensusInstanceValidityCheck(s, new_block_slashing_db)
    ensures && var new_active_block_consensus_instances := 
                        updateConsensusInstanceValidityCheckHelper(
                            s.active_consensus_instances_on_beacon_blocks,
                            new_block_slashing_db
                        );
            && s.block_slashing_db_hist.Keys + new_active_block_consensus_instances.Keys == s'.block_slashing_db_hist.Keys
    { }

    lemma lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state  
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)
    requires inv_available_current_proposer_duty_is_from_dv_seq_of_proposer_duties_body(process, n, sequence_proposer_duties_to_be_served, index_next_proposer_duty_to_be_served)
    requires inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process, index_next_proposer_duty_to_be_served)
    requires pred_last_proposer_duty_is_delivering_to_given_honest_node(proposer_duty, sequence_proposer_duties_to_be_served, n, index_next_proposer_duty_to_be_served)
    ensures inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served)
    {   
        var slot := proposer_duty.slot;
        if  slot in process.future_consensus_instances_on_blocks_already_decided.Keys 
        {
            var new_block_slashing_db := 
                    f_update_block_slashing_db(
                        process.block_slashing_db, 
                        process.future_consensus_instances_on_blocks_already_decided[proposer_duty.slot]
                    );
            lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_updateConsensusInstanceValidityCheck_helper(
                    process.block_consensus_engine_state,
                    new_block_slashing_db,
                    process'.block_consensus_engine_state
            );
            assert inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served);
        }
        else
        {
            // var process_after_adding_new_duty := 
            //     process.(
            //         current_proposer_duty := Some(proposer_duty),
            //         latest_proposer_duty := Some(proposer_duty)
            //     );

            // assert inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process_after_adding_new_duty, index_next_proposer_duty_to_be_served);

            // lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_f_start_consensus_if_can_construct_randao_share(
            //     process_after_adding_new_duty,
            //     process',
            //     sequence_proposer_duties_to_be_served,
            //     n,
            //     index_next_proposer_duty_to_be_served
            // );
            // assert inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served);

            lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_f_start_consensus_if_can_construct_randao_share(
                process,
                process',
                sequence_proposer_duties_to_be_served,
                n,
                index_next_proposer_duty_to_be_served
            );
            assert inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served);
        }            
    }

    lemma lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)
    requires inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process, index_next_proposer_duty_to_be_served)
    requires pred_last_proposer_duty_is_delivering_to_given_honest_node(proposer_duty, sequence_proposer_duties_to_be_served, n, index_next_proposer_duty_to_be_served)
    requires inv_available_current_proposer_duty_is_from_dv_seq_of_proposer_duties_body(process, n, sequence_proposer_duties_to_be_served, index_next_proposer_duty_to_be_served)
    ensures inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served)
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

        lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process',
            sequence_proposer_duties_to_be_served,
            n,
            index_next_proposer_duty_to_be_served
        );
    }

    lemma lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat
    )
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state  
    requires index_next_proposer_duty_to_be_served > 0    
    requires inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process, index_next_proposer_duty_to_be_served-1)
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)
    requires pred_last_proposer_duty_is_delivering_to_given_honest_node(proposer_duty, sequence_proposer_duties_to_be_served, n, index_next_proposer_duty_to_be_served)
    ensures inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served)
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        
        lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty,
            sequence_proposer_duties_to_be_served,
            n,
            index_next_proposer_duty_to_be_served
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process',
            sequence_proposer_duties_to_be_served,
            n,
            index_next_proposer_duty_to_be_served
        );
    }       

    lemma lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock,        
        process': DVCState,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat        
    )
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state
    requires inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(
                sequence_proposer_duties_to_be_served, 
                n, 
                process, 
                index_next_proposer_duty_to_be_served
                )
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)
    ensures inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(
                sequence_proposer_duties_to_be_served, 
                n, 
                process', 
                index_next_proposer_duty_to_be_served
                )
    { }   

    lemma lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat        
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(
                sequence_proposer_duties_to_be_served, 
                n, 
                process, 
                index_next_proposer_duty_to_be_served
                )
    ensures inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(
                sequence_proposer_duties_to_be_served, 
                n, 
                process', 
                index_next_proposer_duty_to_be_served
            )
    { } 

    lemma lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat        
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state        
    requires inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process, index_next_proposer_duty_to_be_served)
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)
    ensures inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served)
    { }   

    lemma lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat        
    )
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process, index_next_proposer_duty_to_be_served)
    ensures inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served)
    { }  

    lemma lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat        
    )
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process, index_next_proposer_duty_to_be_served)
    ensures inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(sequence_proposer_duties_to_be_served, n, process', index_next_proposer_duty_to_be_served)
    { }       

    lemma lem_inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_helper(
        s: DVState,
        event: DV_Block_Proposer_Spec.BlockEvent,
        s': DVState,
        s_node: DVCState,
        n: BLSPubkey
    )
    requires NextEventPreCond(s, event)
    requires NextEvent(s, event, s')      
    requires inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(s.sequence_proposer_duties_to_be_served, n, s_node, s.index_next_proposer_duty_to_be_served)
    ensures inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(s'.sequence_proposer_duties_to_be_served, n, s_node, s.index_next_proposer_duty_to_be_served)
    { }  

    lemma lem_inv_unchanged_rs_f_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    ensures inv_unchanged_rs_body(process, process')
    { }

    lemma lem_inv_unchanged_rs_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    ensures inv_unchanged_rs_body(process, process')
    { }

    lemma lem_inv_unchanged_rs_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    ensures inv_unchanged_rs_body(process, process')
    { }      

    lemma lem_inv_unchanged_rs_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    ensures inv_unchanged_rs_body(process, process')
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
            lem_inv_unchanged_rs_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    } 

    lemma lem_inv_unchanged_rs_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    ensures inv_unchanged_rs_body(process, process')
    { }

    lemma lem_inv_unchanged_rs_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires process.latest_proposer_duty.isPresent()
    ensures inv_unchanged_rs_body(process, process')
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

        lem_inv_unchanged_rs_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_unchanged_rs_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    ensures inv_unchanged_rs_body(process, process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);

        lem_inv_unchanged_rs_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);

        lem_inv_unchanged_rs_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    } 

    lemma lem_inv_unchanged_rs_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    ensures inv_unchanged_rs_body(process, process')
    { }  

    lemma lem_inv_unchanged_rs_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    ensures inv_unchanged_rs_body(process, process')
    { }

    lemma lem_inv_unchanged_rs_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    ensures inv_unchanged_rs_body(process, process')
    { }  

    lemma lem_inv_unchanged_rs_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    ensures inv_unchanged_rs_body(process, process')
    { }  

    lemma lem_inv_unchanged_rs_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    ensures inv_unchanged_rs_body(process, process')
    { } 

    lemma lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share_helper(
        s: BlockConsensusEngineState,
        id: Slot,
        proposer_duty: ProposerDuty,
        block_slashing_db: set<SlashingDBBlock>,
        complete_randao_reveal: BLSSignature,
        s': BlockConsensusEngineState
    )
    requires startConsensusInstance.requires(s, id, proposer_duty, block_slashing_db, complete_randao_reveal)
    requires s' == startConsensusInstance(s, id, proposer_duty, block_slashing_db, complete_randao_reveal)
    ensures s.active_consensus_instances_on_beacon_blocks.Keys + { id } == s'.active_consensus_instances_on_beacon_blocks.Keys
    { }  

    lemma lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState,
        process': DVCState
    )
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process')
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
                assert  && process'.current_proposer_duty.isPresent()
                        && process'.current_proposer_duty.safe_get() == process.current_proposer_duty.safe_get()
                        ;
                assert  process'.latest_proposer_duty.safe_get()
                        ==
                        process.latest_proposer_duty.safe_get();
                lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share_helper(
                    process.block_consensus_engine_state,
                    proposer_duty.slot,
                    proposer_duty,
                    process.block_slashing_db,
                    constructed_randao_reveal.safe_get(),
                    process'.block_consensus_engine_state
                );

                var slot := proposer_duty.slot;

                forall k: Slot | k in process'.block_consensus_engine_state.block_slashing_db_hist.Keys
                ensures k < get_upperlimit_active_instances(process')
                {
                    if k in process.block_consensus_engine_state.block_slashing_db_hist.Keys
                    {
                        assert k < get_upperlimit_active_instances(process);
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

    lemma lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process')
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
            lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }  

    lemma lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state  
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process)
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)  
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process')
    { 
        var slot := proposer_duty.slot;
        if slot in process.future_consensus_instances_on_blocks_already_decided.Keys 
        { }
        else 
        {
            lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
                process,
                process'
            );     
        }
    }  

    lemma lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process)
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)  
    requires process.latest_proposer_duty.isPresent()
    requires get_upperlimit_active_instances(process) <= proposer_duty.slot + 1
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process')
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
        lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state  
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process)
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)  
    requires get_upperlimit_active_instances(process) <= proposer_duty.slot  
    ensures inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        
        lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );   
    }  

    lemma lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock,        
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process)
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)   
    ensures inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process') 
    { }        

    lemma lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process)
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(process)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process')
    { 
        var new_consensus_instances_on_blocks_already_decided: map<Slot, BeaconBlock> := 
            map[ block.slot := block ];

        var consensus_instances_on_blocks_already_decided := process.future_consensus_instances_on_blocks_already_decided + new_consensus_instances_on_blocks_already_decided;

        var future_consensus_instances_on_blocks_already_decided := 
            f_listen_for_new_imported_blocks_helper(process, consensus_instances_on_blocks_already_decided);

        var process_after_stopping_consensus_instance :=
            process.(
                future_consensus_instances_on_blocks_already_decided := future_consensus_instances_on_blocks_already_decided,
                block_consensus_engine_state := stopConsensusInstances(
                                process.block_consensus_engine_state,
                                consensus_instances_on_blocks_already_decided.Keys
                ),
                block_shares_to_broadcast := process.block_shares_to_broadcast - consensus_instances_on_blocks_already_decided.Keys,
                rcvd_block_shares := process.rcvd_block_shares - consensus_instances_on_blocks_already_decided.Keys                    
            );  

        assert  inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process_after_stopping_consensus_instance); 

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
            assert  get_upperlimit_active_instances(process)
                    ==
                    get_upperlimit_active_instances(process_after_stopping_consensus_instance)
                    ==
                    get_upperlimit_active_instances(process')
                    ;

            var blocks := consensus_instances_on_blocks_already_decided[process.current_proposer_duty.safe_get().slot];
            var new_block_slashing_db := 
                f_update_block_slashing_db(process.block_slashing_db, block);      
            var new_active_consensus_instances_on_beacon_blocks := 
                updateConsensusInstanceValidityCheckHelper(
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
            assert  new_active_consensus_instances_on_beacon_blocks.Keys
                    <=
                    process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys
                    ;
            assert  process.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys
                    <=
                    process.block_consensus_engine_state.block_slashing_db_hist.Keys
                    ;
                
            
            forall k: Slot | k in process'.block_consensus_engine_state.block_slashing_db_hist.Keys 
            ensures k < get_upperlimit_active_instances(process')
            {
                if k in process.block_consensus_engine_state.block_slashing_db_hist.Keys
                {
                    assert k < get_upperlimit_active_instances(process');
                }
                else
                {
                    assert k == process'.latest_proposer_duty.safe_get().slot;
                    assert k < get_upperlimit_active_instances(process');                    
                }
            }
            
            assert  inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process'); 
        }
        else
        {
            assert  inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process');
        }
    }  

    lemma lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body_f_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState,
        dv: DVState,
        n: BLSPubkey
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block) 
    requires inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process)
    ensures inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process')
    { }      

    lemma lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState,
        dv: DVState,
        n: BLSPubkey
    )
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state   
    requires inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process)
    ensures inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process')
    { }    

    lemma lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body_f_listen_for_randao_shares(
        process: DVCState,
        randao_share: RandaoShare,
        process': DVCState,
        dv: DVState,
        n: BLSPubkey
    )
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process)
    ensures inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process')
    { }    

    lemma lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState,
        dv: DVState,
        n: BLSPubkey
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state   
    requires inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process)
    ensures inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process')
    { }    

    lemma lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        decided_beacon_block: BeaconBlock,        
        process': DVCState,
        dv: DVState,
        n: BLSPubkey
    )
    requires f_block_consensus_decided.requires(process, id, decided_beacon_block)
    requires process' == f_block_consensus_decided(process, id, decided_beacon_block).state
    requires inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process)
    ensures inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process'); 
    { }  

    lemma lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        s': DVCState,
        dv: DVState,
        n: BLSPubkey
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires s' == f_check_for_next_duty(process, proposer_duty).state  
    requires inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, process)
    ensures inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(dv, n, s')
    { } 



    lemma lem_inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        s': DVCState,
        dv: DVState,
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
        process: DVCState,
        block: BeaconBlock,
        process': DVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
    { }

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
    { }

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
    { }      

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
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
            lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
    { }

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
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

        lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        
        lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );
    } 

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
    { }  

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
    { }

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
    { }  

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
    { }  

    lemma lem_inv_stored_SlashingDBBlocks_have_available_signing_root_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_stored_SlashingDBBlocks_have_available_signing_root_body(process)
    ensures inv_stored_SlashingDBBlocks_have_available_signing_root_body(process')
    { }

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process')
    { }

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process')
    { }

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process')
    { }      

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process')
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
            lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process')
    { }

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process')
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

        lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        
        lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );
    } 

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
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
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process')
    { }

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
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
                    block_consensus_engine_state := stopConsensusInstances(
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

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process')
    { }  

    lemma lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process')
    { }  

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
    { } 

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
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
            lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    } 

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires && process.latest_proposer_duty.isPresent()
             && process.latest_proposer_duty.safe_get().slot == proposer_duty.slot
    requires inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
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

            assert  inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process');
        }
        else 
        {
            lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_start_consensus_if_can_construct_randao_share(
                process,
                process'
            );
        }
            
    }

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    requires && process.latest_proposer_duty.isPresent()
             && process.latest_proposer_duty.safe_get().slot == proposer_duty.slot
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
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

        lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    requires inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    requires inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty_body(process, proposer_duty)
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        
        lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        lem_inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);

        assert  process_after_receiving_duty.latest_proposer_duty.isPresent();                

        assert  process_after_receiving_duty.block_slashing_db
                ==
                process_after_stopping_current_duty.block_slashing_db
                ;

        if  !process_after_stopping_current_duty.latest_proposer_duty.isPresent()
        {
            assert  process_after_receiving_duty.block_slashing_db == {};
            assert  inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process_after_receiving_duty);
        }
        else
        {
            assert  inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process_after_receiving_duty);
        }
       
        lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );
    } 

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    requires inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
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
            var fork_version := bn_get_fork_version(block.slot);
            var block_signature := rs_sign_block(block, fork_version, block_signing_root, process.rs);
            var block_share := SignedBeaconBlock(block, block_signature);
            var process_after_updating_block_shares_to_broadcast := 
                process.(                
                    block_shares_to_broadcast := process.block_shares_to_broadcast[slot := block_share],
                    block_slashing_db := new_block_slashing_db,
                    block_consensus_engine_state := updateConsensusInstanceValidityCheck(
                                                        process.block_consensus_engine_state,
                                                        new_block_slashing_db
                                                    ),
                    latest_slashing_db_block := Some(new_slashingDB_block)
                );
            
        }
        else
        { }
    }  

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
    { }

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    requires inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
    { 
        var new_consensus_instances_on_blocks_already_decided: map<Slot, BeaconBlock> := 
            map[ block.slot := block ];

        var consensus_instances_on_blocks_already_decided := process.future_consensus_instances_on_blocks_already_decided + new_consensus_instances_on_blocks_already_decided;

        var future_consensus_instances_on_blocks_already_decided := 
            f_listen_for_new_imported_blocks_helper(process, consensus_instances_on_blocks_already_decided);

        var process_after_stopping_consensus_instance :=
                process.(
                    future_consensus_instances_on_blocks_already_decided := future_consensus_instances_on_blocks_already_decided,
                    block_consensus_engine_state := stopConsensusInstances(
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

            assert  inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process');
        }
        else
        { 
            assert  inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process');
        }
    }  

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    ensures inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process')
    { }  

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_add_block_to_bn(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState 
    )
    requires f_add_block_to_bn.requires(process, block)
    requires process' == f_add_block_to_bn(process, block)    
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
    { }

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_terminate_current_proposer_duty(
        process: DVCState,
        process': DVCState
    )
    requires f_terminate_current_proposer_duty.requires(process)
    requires process' == f_terminate_current_proposer_duty(process)
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
    { }

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_start_consensus_if_can_construct_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_start_consensus_if_can_construct_randao_share.requires(process)
    requires process' == f_start_consensus_if_can_construct_randao_share(process).state    
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
    { }      

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_listen_for_randao_shares(
        process: DVCState, 
        randao_share: RandaoShare,
        process': DVCState)
    requires f_listen_for_randao_shares.requires(process, randao_share)
    requires process' == f_listen_for_randao_shares(process, randao_share).state   
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
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
            lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_start_consensus_if_can_construct_randao_share(
                process_with_new_randao_share,
                process'
            );
        }
        else
        { }
    }      

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_check_for_next_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )
    requires f_check_for_next_duty.requires(process, proposer_duty)
    requires process' == f_check_for_next_duty(process, proposer_duty).state
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
    { }

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
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

        lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_check_for_next_duty(
            process_after_adding_randao_share,
            proposer_duty,
            process'
        );
    }

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_serve_proposer_duty(
        process: DVCState,
        proposer_duty: ProposerDuty,
        process': DVCState
    )  
    requires f_serve_proposer_duty.requires(process, proposer_duty)
    requires process' == f_serve_proposer_duty(process, proposer_duty).state
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        
        lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
       
        lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_broadcast_randao_share(
            process_after_receiving_duty,
            proposer_duty,
            process'
        );
    } 

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_block_consensus_decided(
        process: DVCState,
        id: Slot,
        block: BeaconBlock, 
        process': DVCState
    )
    requires f_block_consensus_decided.requires(process, id, block)
    requires process' == f_block_consensus_decided(process, id, block).state 
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
    { }  

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_listen_for_block_signature_shares(
        process: DVCState,
        block_share: SignedBeaconBlock,
        process': DVCState
    )
    requires f_listen_for_block_signature_shares.requires(process, block_share)
    requires process' == f_listen_for_block_signature_shares(process, block_share).state
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
    { }

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_listen_for_new_imported_blocks(
        process: DVCState,
        block: BeaconBlock,
        process': DVCState
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
    { }  

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_resend_randao_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_randao_share.requires(process)
    requires process' == f_resend_randao_share(process).state    
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
    { }  

    lemma lem_inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body_f_resend_block_share(
        process: DVCState, 
        process': DVCState)
    requires f_resend_block_share.requires(process)
    requires process' == f_resend_block_share(process).state    
    requires inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process)
    ensures inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(process')
    { }  

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
    requires && process.latest_proposer_duty.isPresent()
             && process.latest_proposer_duty.safe_get().slot <= proposer_duty.slot
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    requires inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    requires inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process')
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

            assert inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process');
        }
        else 
        { }
    }

    lemma lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_broadcast_randao_share(
        process: DVCState,
        proposer_duty: ProposerDuty, 
        process': DVCState
    )
    requires f_broadcast_randao_share.requires(process, proposer_duty)
    requires process' == f_broadcast_randao_share(process, proposer_duty).state
    requires && process.latest_proposer_duty.isPresent()
             && process.latest_proposer_duty.safe_get().slot <= proposer_duty.slot
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    requires inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
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
    requires inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty_body(process, proposer_duty)
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    requires inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    requires inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(process)
    requires inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process')
    {
        var process_after_stopping_current_duty := f_terminate_current_proposer_duty(process);
        
        lem_inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body_f_terminate_current_proposer_duty(
            process,
            process_after_stopping_current_duty
        );

        assert  inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process_after_stopping_current_duty);
        
        if process_after_stopping_current_duty.latest_proposer_duty.isPresent()
        {
            assert  process_after_stopping_current_duty.latest_proposer_duty.safe_get().slot < proposer_duty.slot;
        }

        var process_after_receiving_duty := 
            f_receive_new_duty(process_after_stopping_current_duty, proposer_duty);
        var slot := proposer_duty.slot;

        assert  && process_after_receiving_duty.latest_proposer_duty.isPresent()
                && process_after_receiving_duty.latest_proposer_duty.safe_get().slot == slot
                ;
        assert  inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process_after_receiving_duty);

        forall slashing_db_block | slashing_db_block in process_after_receiving_duty.block_slashing_db
        ensures slashing_db_block.slot < slot;
        {
            assert  slashing_db_block in process_after_stopping_current_duty.block_slashing_db;
            assert  slashing_db_block in process.block_slashing_db;
            assert  process.latest_proposer_duty.isPresent();
            assert  slashing_db_block.slot <= process.latest_proposer_duty.safe_get().slot;
            assert  slashing_db_block.slot < slot;
        }

        assert  inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process_after_receiving_duty);        
       
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
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    requires inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    requires inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process')
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

            lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_block_consensus_decided(
                process, 
                id, 
                block, 
                process'
            );               
        }
        else
        { }
    }  

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
    requires inv_slots_in_future_decided_beacon_blocks_are_correct_body(process)
    requires inv_available_current_proposer_duty_is_latest_proposer_duty_body(process)
    requires inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(process)
    requires inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process)
    ensures inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(process')
    { 
        var new_consensus_instances_on_blocks_already_decided: map<Slot, BeaconBlock> := 
            map[ block.slot := block ];

        var consensus_instances_on_blocks_already_decided := process.future_consensus_instances_on_blocks_already_decided + new_consensus_instances_on_blocks_already_decided;

        var future_consensus_instances_on_blocks_already_decided := 
            f_listen_for_new_imported_blocks_helper(process, consensus_instances_on_blocks_already_decided);

        var process_after_stopping_consensus_instance :=
            process.(
                future_consensus_instances_on_blocks_already_decided := future_consensus_instances_on_blocks_already_decided,
                block_consensus_engine_state := stopConsensusInstances(
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
            
            lem_inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body_f_listen_for_new_imported_blocks(
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
}