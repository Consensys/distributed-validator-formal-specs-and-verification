include "../../../common/block_proposer/block_types.dfy"
include "../../../common/block_proposer/block_common_functions.dfy"
include "../../../common/block_proposer/block_signing_functions.dfy"
include "../../../specs/consensus/block_consensus.dfy"
include "../../../specs/network/block_network.dfy"
include "../../../specs/dv/dv_block_proposer.dfy"
include "../common/dvc_block_proposer_instrumented.dfy"
include "../../common/helper_sets_lemmas.dfy"
include "../common/block_dvc_spec_axioms.dfy"



module Block_Inv_With_Empty_Initial_Block_Slashing_DB
{
    import opened Block_Types 
    import opened Block_Common_Functions
    import opened Block_Signing_Functions
    import opened Block_Consensus_Spec
    import opened Block_Network_Spec
    import opened DVC_Block_Proposer_Spec_Instr
    import opened DV_Block_Proposer_Spec
    import opened Helper_Sets_Lemmas
    import opened DVC_Block_Proposer_Spec_Axioms


    predicate is_honest_node(s: DVState, n: BLSPubkey)
    {
        && n in s.honest_nodes_states.Keys
    }

    predicate inv_quorum_constraints(dv: DVState)
    {        
        && var all_nodes := dv.all_nodes;
        && var honest_nodes := dv.honest_nodes_states.Keys;
        && var dishonest_nodes := dv.adversary.nodes;
        && 0 < |all_nodes|
        && quorum(|all_nodes|) <= |honest_nodes|
        && |dishonest_nodes| <= f(|all_nodes|) 
        && all_nodes == honest_nodes + dishonest_nodes
        && honest_nodes * dishonest_nodes == {}
    }

    predicate inv_unchanged_paras_of_consensus_instances(dv: DVState)
    {
        forall ci | ci in dv.consensus_instances_on_beacon_block.Values
            :: && ci.all_nodes == dv.all_nodes
               && ci.honest_nodes_status.Keys == dv.honest_nodes_states.Keys  
               && ci.honest_nodes_status.Keys <= ci.all_nodes
               && ci.honest_nodes_validity_functions.Keys <= ci.honest_nodes_status.Keys
               && |ci.all_nodes - ci.honest_nodes_status.Keys| <= f(|ci.all_nodes|)
    }

    predicate same_honest_nodes_in_dv_and_ci(dv: DVState)
    {
        forall s: Slot ::
            && var ci := dv.consensus_instances_on_beacon_block[s];            
            && dv.all_nodes == ci.all_nodes
            && dv.honest_nodes_states.Keys == ci.honest_nodes_status.Keys
    }

    predicate inv_current_proposer_duty_is_rcvd_duty_body(dvc: DVCState)
    {
        dvc.current_proposer_duty.isPresent()
        ==> 
        dvc.current_proposer_duty.safe_get() in dvc.all_rcvd_duties
    }

    predicate inv_current_proposer_duty_is_rcvd_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_current_proposer_duty_is_rcvd_duty_body(dvc)
    }

    predicate inv_only_dv_construct_complete_signed_block(dv: DVState)
    {
        && construct_complete_signed_block_assumptions(dv)                
        && forall n | n in dv.honest_nodes_states.Keys :: 
                && var nodes := dv.honest_nodes_states[n];
                && nodes.construct_complete_signed_block == dv.construct_complete_signed_block
                && nodes.dv_pubkey == dv.dv_pubkey       
                && nodes.peers == dv.all_nodes
    }

    predicate inv_only_dv_construct_complete_signed_randao_reveal(dv: DVState)
    {
        && construct_complete_signed_randao_reveal_assumptions(dv)                
        && forall n | n in dv.honest_nodes_states.Keys :: 
                && var nodes := dv.honest_nodes_states[n];
                && nodes.construct_complete_signed_randao_reveal == dv.construct_complete_signed_randao_reveal
                && nodes.dv_pubkey == dv.dv_pubkey       
                && nodes.peers == dv.all_nodes
    }

    predicate inv_only_dv_construct_complete_signature_functions(dv: DVState)
    {
        && inv_only_dv_construct_complete_signed_randao_reveal(dv)
        && inv_only_dv_construct_complete_signed_block(dv)                
    }

    predicate inv_latest_served_duty_is_rcvd_duty_body(dvc: DVCState)
    {
        dvc.latest_proposer_duty.isPresent()
        ==> 
        dvc.latest_proposer_duty.safe_get() in dvc.all_rcvd_duties
    }

    predicate inv_latest_served_duty_is_rcvd_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_latest_served_duty_is_rcvd_duty_body(dvc)
    }

    predicate inv_none_latest_served_duty_implies_none_current_proposer_duty_body(dvc: DVCState)
    {
        !dvc.latest_proposer_duty.isPresent()
        ==> 
        !dvc.current_proposer_duty.isPresent()
    }

    predicate inv_none_latest_served_duty_implies_none_current_proposer_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_none_latest_served_duty_implies_none_current_proposer_duty_body(dvc)
    }

    predicate inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(dvc: DVCState)
    {
        !dvc.latest_proposer_duty.isPresent()
        ==> 
        ( || !dvc.current_proposer_duty.isPresent()
          || ( && dvc.latest_proposer_duty.isPresent()
               && dvc.current_proposer_duty.isPresent()
               && dvc.current_proposer_duty.safe_get()
                    == dvc.latest_proposer_duty.safe_get()
             )
        )
    }

    predicate inv_current_proposer_duty_is_either_none_or_latest_served_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_current_proposer_duty_is_either_none_or_latest_served_duty_body(dvc)
    }

    predicate inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(dvc: DVCState)
    {
        dvc.current_proposer_duty.isPresent()
        ==> 
        ( && dvc.latest_proposer_duty.isPresent()
          && dvc.current_proposer_duty.safe_get()
                                == dvc.latest_proposer_duty.safe_get()                   
        )
    }

    predicate inv_available_current_proposer_duty_is_latest_served_proposer_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_available_current_proposer_duty_is_latest_served_proposer_duty_body(dvc)
    }

    predicate inv_seq_of_proposer_duties_is_ordered(dv: DVState)
    {
        proposer_duties_are_ordered(dv)
    }

    predicate inv_no_duplicated_proposer_duties(dv: DVState)
    {        
        forall k1: Slot, k2: Slot ::
                && 0 <= k1
                && k1 < k2
                && dv.sequence_proposer_duties_to_be_served[k1].node 
                        in dv.honest_nodes_states.Keys
                && dv.sequence_proposer_duties_to_be_served[k1].node 
                        == dv.sequence_proposer_duties_to_be_served[k2].node 
                ==> 
                && var duty1 := dv.sequence_proposer_duties_to_be_served[k1].proposer_duty;
                && var duty2 := dv.sequence_proposer_duties_to_be_served[k2].proposer_duty;
                && duty1.slot < duty2.slot
    }

    predicate inv_unchanged_dvn_seq_of_proposer_duties(dv: DVState, dv': DVState)
    {
        dv.sequence_proposer_duties_to_be_served
                == dv'.sequence_proposer_duties_to_be_served
    }

    predicate inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(dvc: DVCState)
    {
        !dvc.latest_proposer_duty.isPresent()
        ==> 
        dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys == {}
    }

    predicate inv_no_active_consensus_instance_before_receiving_a_proposer_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_no_active_consensus_instance_before_receiving_a_proposer_duty_body(dvc)
    }

    predicate pred_proposer_duty_is_from_dv_seq_of_proposer_duties_new_body(  
        proposer_duty: ProposerDuty,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    {
        exists i: Slot :: 
            && i < index_next_proposer_duty_to_be_served
            && var an := sequence_proposer_duties_to_be_served[i];
            && an.proposer_duty == proposer_duty
            && an.node == hn
    }     

    predicate inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(  
        n: BLSPubkey,
        n_state: DVCState,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    {
        n_state.latest_proposer_duty.isPresent()
        ==>
        exists i: Slot :: 
            && i < index_next_proposer_duty_to_be_served
            && var an := sequence_proposer_duties_to_be_served[i];
            && an.proposer_duty == n_state.latest_proposer_duty.safe_get()
            && an.node == n
    }  

    predicate inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn],
                dv.index_next_proposer_duty_to_be_served
            )                    
    }               

    predicate inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState,
        index_next_proposer_duty_to_be_served: nat
    )
    {
        n_state.latest_proposer_duty.isPresent() ==>
            exists i: Slot :: 
                && i < index_next_proposer_duty_to_be_served
                && var an := dv.sequence_proposer_duties_to_be_served[i];
                && an.proposer_duty == n_state.latest_proposer_duty.safe_get()
                && an.node == n
    }  

    predicate inv_every_proposer_duty_before_dvn_proposer_index_was_delivered_body(dvc: DVCState, duty: ProposerDuty)
    {
        duty in dvc.all_rcvd_duties
    }

    predicate inv_every_proposer_duty_before_dvn_proposer_index_was_delivered(dv: DVState)
    {
        forall k: nat ::
            && 0 <= k < dv.index_next_proposer_duty_to_be_served
            && dv.sequence_proposer_duties_to_be_served[k].node in dv.honest_nodes_states.Keys
            ==> 
            && var duty_and_node: ProposerDutyAndNode := dv.sequence_proposer_duties_to_be_served[k];
            && var duty := duty_and_node.proposer_duty;
            && var hn := duty_and_node.node;
            && var dvc := dv.honest_nodes_states[hn];
            && inv_every_proposer_duty_before_dvn_proposer_index_was_delivered_body(dvc, duty)
    }   

    predicate inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(dvc: DVCState)
    {
        forall k: Slot | k in dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys ::
            exists rcvd_duty: ProposerDuty :: 
                && rcvd_duty in dvc.all_rcvd_duties
                && rcvd_duty.slot == k
    }

    predicate inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_consensus_instance_only_for_slot_in_which_dvc_has_rcvd_proposer_duty_body(dvc)
    }

    predicate inv_consensus_instances_only_for_rcvd_duties_body(dvc: DVCState)
    {
        forall k: Slot | k in dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys 
            ::
            && dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[k].proposer_duty in dvc.all_rcvd_duties                
            && dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[k].proposer_duty.slot == k
    }

    predicate inv_consensus_instances_only_for_rcvd_duties(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_consensus_instances_only_for_rcvd_duties_body(dvc)
    }
             
    predicate inv_the_latest_proposer_duty_was_sent_from_dv(
        s': DVState,
        index_next_proposer_duty_to_be_served: nat,
        proposer_duty: ProposerDuty,
        node: BLSPubkey
    )
    {
        && index_next_proposer_duty_to_be_served > 0
        && var an := s'.sequence_proposer_duties_to_be_served[index_next_proposer_duty_to_be_served - 1];
        && proposer_duty == an.proposer_duty
        && node == an.node    
    }   

    predicate inv_all_in_transit_messages_were_sent_body<M>(e: Network<M>)
    {
         forall m | m in e.messagesInTransit::
                m.message in e.allMessagesSent       
    } 
     
    predicate inv_all_in_transit_messages_were_sent(dv: DVState)
    {
         forall m | m in dv.block_share_network.messagesInTransit::
                m.message in dv.block_share_network.allMessagesSent       
    } 

    predicate inv_rcvd_block_shares_are_in_all_sent_messages_body(
        dv: DVState,
        dvc: DVCState
    )
    {
        var rcvd_block_shares := dvc.rcvd_block_shares;

        forall i, j |
            && i in rcvd_block_shares.Keys 
            && j in rcvd_block_shares[i]
            ::
            rcvd_block_shares[i][j] <= dv.block_share_network.allMessagesSent
    }
    
    predicate invNetwork(
        dv: DVState
    )
    {
        forall m | m in dv.block_share_network.messagesInTransit
            ::
            m.message in dv.block_share_network.allMessagesSent       
    }

    predicate inv_rcvd_block_shares_are_in_all_sent_messages(
        dv: DVState
    )
    {
        forall hn: BLSPubkey | is_honest_node(dv, hn) ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_rcvd_block_shares_are_in_all_sent_messages_body(dv, dvc)
        
    }

    predicate inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(
        dv: DVState,
        hn: BLSPubkey, 
        block_share: SignedBeaconBlock,
        complete_signed_block: SignedBeaconBlock
    )
    {
        && hn in dv.honest_nodes_states.Keys 
        && block_share in dv.block_share_network.allMessagesSent
        && block_share.block == complete_signed_block.block
        && var block_signing_root := compute_block_signing_root(block_share.block);                                      
        && verify_bls_signature(block_signing_root, block_share.signature, hn)
    }

    predicate inv_exists_honest_dvc_that_sent_block_share_for_submitted_block(dv: DVState)
    {
        forall block: SignedBeaconBlock |
            block in dv.all_blocks_created            
            ::
            exists hn, block_share: SignedBeaconBlock 
                :: 
                inv_exists_honest_dvc_that_sent_block_share_for_submitted_block_body(dv, hn, block_share, block)
    }
   




    predicate inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_body(
        dvc: DVCState,
        cid: Slot
    )
    requires cid in dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks
    {
        var bci := dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid];
        inv_existing_block_slashing_db_and_randao_reveal_for_sent_vp(
            cid, 
            bci.proposer_duty, 
            bci.randao_reveal,
            bci.validityPredicate            
        ) 
    }     

   

    predicate inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc(
        dvc: DVCState
    )
    {
        forall cid | 
            cid in dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks
            ::
            inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_body(dvc, cid)        
    }    

    predicate inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(
        s: Slot,
        proposer_duty: ProposerDuty,        
        block_slashing_db: set<SlashingDBBlock>,
        randao_reveal: BLSSignature,
        vp: BeaconBlock -> bool
    )
    {
        && proposer_duty.slot == s
        && (vp ==   (block: BeaconBlock) 
                    => 
                    ci_decision_is_valid_beacon_block(
                        block_slashing_db, 
                        block, 
                        proposer_duty, 
                        randao_reveal
                    )
            )
    }

    predicate inv_existing_block_slashing_db_and_randao_reveal_for_sent_vp(
        cid: Slot,
        proposer_duty: ProposerDuty,
        randao_reveal: BLSSignature,
        vp: BeaconBlock -> bool        
    )
    {
        exists  block_slashing_db: set<SlashingDBBlock>, randao_reveal: BLSSignature
                ::
                inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(
                    cid, 
                    proposer_duty,                 
                    block_slashing_db, 
                    randao_reveal,
                    vp
                )
    }      

    predicate inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc(
        dv: DVState,
        n: BLSPubkey,
        cid: Slot
    )
    requires n in dv.honest_nodes_states.Keys 
    requires cid in dv.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks
    {
        && var dvc := dv.honest_nodes_states[n];
        && var bci := dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid];
        && inv_existing_block_slashing_db_and_randao_reveal_for_sent_vp(
                cid, 
                bci.proposer_duty, 
                bci.randao_reveal,
                bci.validityPredicate
            ) 
    }

    predicate inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dv(
        dv: DVState
    )
    {
        forall n, cid | 
            && n in dv.honest_nodes_states 
            && cid in dv.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks
            ::
            inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc(dv, n, cid)
    }

    predicate inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal(dv: DVState)
    {
        forall hn, s: Slot, vp |
            && hn in dv.consensus_instances_on_beacon_block[s].honest_nodes_validity_functions.Keys
            && vp in dv.consensus_instances_on_beacon_block[s].honest_nodes_validity_functions[hn]
            ::
            exists proposer_duty, block_slashing_db, randao_reveal ::
                inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(
                    s, 
                    proposer_duty, 
                    block_slashing_db, 
                    randao_reveal,
                    vp
                )
    }   


    predicate inv_decided_value_of_consensus_instance_is_decided_by_quorum(dv: DVState)
    {
        forall cid |
            && cid in dv.consensus_instances_on_beacon_block.Keys
            && dv.consensus_instances_on_beacon_block[cid].decided_value.isPresent()
            ::
            is_a_valid_decided_value(dv.consensus_instances_on_beacon_block[cid])
    }  

    predicate inv_decided_value_of_consensus_instance_of_slot_k_is_for_slot_k(dv: DVState)
    {
        forall cid |
            && cid in dv.consensus_instances_on_beacon_block.Keys
            && dv.consensus_instances_on_beacon_block[cid].decided_value.isPresent()
            ::
            dv.consensus_instances_on_beacon_block[cid].decided_value.safe_get().slot == cid
    }   

    predicate inv_block_of_block_share_is_decided_value(dv: DVState)
    {
        forall hn, block_share |
                && hn in dv.honest_nodes_states.Keys 
                && block_share in dv.block_share_network.allMessagesSent
                && var block_signing_root := compute_block_signing_root(block_share.block);                                      
                && verify_bls_signature(block_signing_root, block_share.signature, hn)
                ::
                inv_block_of_block_share_is_decided_value_body(dv, block_share)
    }  

    predicate inv_block_of_block_share_is_decided_value_body(dv: DVState, block_share: SignedBeaconBlock)
    {
        && dv.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.isPresent()
        && dv.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.safe_get() == block_share.block
    }  

    // predicate inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_proposer_duties_body(dvc: DVCState, next_duty: ProposerDuty)
    // {
    //    forall rcvd_duty: ProposerDuty | rcvd_duty in dvc.all_rcvd_duties ::
    //         rcvd_duty.slot <= next_duty.slot        
    // }

    // predicate inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_proposer_duties(dv: DVState)
    // {
    //     && var dv_duty_queue := dv.sequence_proposer_duties_to_be_served;
    //     && var dv_index := dv.index_next_proposer_duty_to_be_served;
    //     && var next_duty_and_node := dv_duty_queue[dv_index];
    //     && forall hn: BLSPubkey | 
    //         && hn in dv.honest_nodes_states.Keys
    //         && hn == next_duty_and_node.node 
    //         ::            
    //         && var dvc := dv.honest_nodes_states[hn];
    //         && var next_duty := next_duty_and_node.proposer_duty;
    //         && inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_proposer_duties_body(dvc, next_duty)
    // }
                  


    // predicate inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(dvc: DVCState)
    // {
    //     dvc.latest_proposer_duty.isPresent()
    //     ==> ( forall k: Slot | k in dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys 
    //             ::
    //             k <= dvc.latest_proposer_duty.safe_get().slot
    //         )
    // }

    // predicate inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty(dv: DVState)
    // {
    //     forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
    //         && var dvc := dv.honest_nodes_states[hn];
    //         && inv_slot_of_active_consensus_instance_is_not_higher_than_slot_of_latest_served_proposer_duty_body(dvc)
    // }



    // predicate inv_rcvd_block_shares_are_in_all_messages_sent_single_node(
    //     dv: DVState,
    //     n: BLSPubkey
    // )
    // requires n in dv.honest_nodes_states.Keys
    // {
    //     inv_rcvd_block_shares_are_in_all_sent_messages_body(
    //         dv,
    //         dv.honest_nodes_states[n]
    //     )
    // }

    // predicate inv_rcvd_block_shares_are_in_all_messages_sent(
    //     dv: DVState    
    // )
    // {
    //     forall n |
    //         n in dv.honest_nodes_states
    //         ::
    //         inv_rcvd_block_shares_are_in_all_messages_sent_single_node(dv, n)
    // }  

    






  

    


 

       

    // predicate inv_exists_proposer_duty_in_dv_seq_of_proposer_duty_for_every_slot_in_block_slashing_db_hist(dv: DVState)    
    // {
    //     forall hn |
    //         && hn in dv.honest_nodes_states.Keys          
    //         ::
    //         inv_exists_proposer_duty_in_dv_seq_of_proposer_duty_for_every_slot_in_block_slashing_db_hist_body(
    //             dv, 
    //             hn,
    //             dv.honest_nodes_states[hn],
    //             dv.index_next_proposer_duty_to_be_served
    //         )                    
    // }       

    // predicate inv_exists_proposer_duty_in_dv_seq_of_proposer_duty_for_every_slot_in_block_slashing_db_hist_body(
    //     dv: DVState, 
    //     n: BLSPubkey,
    //     n_state: DVCState,
    //     index_next_proposer_duty_to_be_served: nat
    // )
    // {
    //     forall slot  |
    //         && slot in n_state.block_consensus_engine_state.block_slashing_db_hist
    //         ::
    //         exists i: Slot :: 
    //             && i < index_next_proposer_duty_to_be_served
    //             && var an := dv.sequence_proposer_duties_to_be_served[i];
    //             && an.proposer_duty.slot == slot 
    //             && an.node == n
    // }   

    // predicate inv_exists_proposer_duty_in_dv_seq_of_proposer_duty_for_every_slot_in_block_slashing_db_hist_a(dv: DVState)    
    // {
    //     forall hn |
    //         && hn in dv.honest_nodes_states.Keys          
    //         ::
    //         inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_proposer_duty(
    //             dv, 
    //             hn,
    //             dv.honest_nodes_states[hn]
    //         )                    
    // }   

    // function get_upperlimit_active_instances(
    //     n_state: DVCState
    // ): nat 
    // {
    //     if n_state.latest_proposer_duty.isPresent() then
    //         n_state.latest_proposer_duty.safe_get().slot + 1
    //     else
    //         0
    // }                

    // predicate inv_slot_of_consensus_instance_is_up_to_slot_of_latest_served_proposer_duty(
    //     dv: DVState, 
    //     n: BLSPubkey,
    //     n_state: DVCState
    // )
    // {
    //     forall slot  |
    //         && slot in n_state.block_consensus_engine_state.block_slashing_db_hist
    //         ::
    //         slot < get_upperlimit_active_instances(n_state)
    // }      

    // predicate inv_slot_of_consensus_instance_is_up_to_slot_of_latest_proposer_duty_body(
    //     dvc: DVCState       
    // )
    // {
    //     forall slot: Slot |
    //         && slot in dvc.block_consensus_engine_state.block_slashing_db_hist
    //         ::
    //         slot < get_upperlimit_active_instances(dvc)
    // }     

    // predicate inv_slot_of_consensus_instance_is_up_to_slot_of_latest_proposer_duty(
    //     dv: DVState        
    // )
    // {
    //     forall hn: BLSPubkey | is_honest_node(dv, hn) ::
    //             inv_slot_of_consensus_instance_is_up_to_slot_of_latest_proposer_duty_body(dv.honest_nodes_states[hn])        
    // }     
    
        





    // function get_upperlimit_decided_instances(
    //     n_state: DVCState
    // ): nat 
    // {
    //     if n_state.latest_proposer_duty.isPresent() then
    //         if n_state.current_proposer_duty.isPresent() then 
    //             n_state.latest_proposer_duty.safe_get().slot
    //         else
    //             n_state.latest_proposer_duty.safe_get().slot + 1
    //     else
    //         0
    // }

    // predicate inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv(dv: DVState)    
    // {
    //     forall hn |
    //         && hn in dv.honest_nodes_states.Keys          
    //         ::
    //         inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(
    //             dv, 
    //             hn,
    //             dv.honest_nodes_states[hn]
    //         )                    
    // }       

    // predicate inv_future_decided_data_of_dvc_is_consistent_with_existing_decision_dv_body(
    //     dv: DVState, 
    //     n: BLSPubkey,
    //     n_state: DVCState
    // )
    // {
    //     forall slot |
    //         && slot in n_state.future_proposer_consensus_instances_already_decided.Keys
    //         ::
    //         && dv.consensus_instances_on_beacon_block[slot].decided_value.isPresent()
    //         && n_state.future_proposer_consensus_instances_already_decided[slot] == dv.consensus_instances_on_beacon_block[slot].decided_value.safe_get()
    // }  

    // predicate inv_slot_in_future_decided_data_is_correct(dv: DVState)    
    // {
    //     forall hn |
    //         && hn in dv.honest_nodes_states.Keys          
    //         ::
    //         inv_slot_in_future_decided_data_is_correct_body(
    //             dv, 
    //             hn,
    //             dv.honest_nodes_states[hn]
    //         )                    
    // }              

    // predicate inv_slot_in_future_decided_data_is_correct_body(
    //     dv: DVState, 
    //     n: BLSPubkey,
    //     n_state: DVCState
    // )
    // {
    //     forall slot |
    //         && slot in n_state.future_proposer_consensus_instances_already_decided
    //         ::
    //         n_state.future_proposer_consensus_instances_already_decided[slot].slot == slot
    // }       

    // predicate inv_active_consensus_instances_on_beacon_blocks_keys_is_subset_of_block_slashing_db_hist(dv: DVState)    
    // {
    //     forall hn |
    //         && hn in dv.honest_nodes_states.Keys          
    //         ::
    //         inv_active_consensus_instances_on_beacon_blocks_keys_is_subset_of_block_slashing_db_hist_body_body(
    //             dv.honest_nodes_states[hn]
    //         )                    
    // }       

    // predicate inv_active_consensus_instances_on_beacon_blocks_keys_is_subset_of_block_slashing_db_hist_body_body
    // (
    //     n_state: DVCState
    // )
    // {
    //     n_state.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys <= n_state.block_consensus_engine_state.block_slashing_db_hist.Keys
    // }

    // predicate inv_active_consensus_instances_on_beacon_blocks_predicate_is_in_block_slashing_db_hist(dv: DVState)    
    // {
    //     forall hn, cid |
    //         && hn in dv.honest_nodes_states.Keys        
    //         ::
    //         inv_active_consensus_instances_on_beacon_blocks_predicate_is_in_block_slashing_db_hist_body(dv.honest_nodes_states[hn], cid)
             
    // }       

    // predicate inv_active_consensus_instances_on_beacon_blocks_predicate_is_in_block_slashing_db_hist_body
    // (
    //     n_state: DVCState,
    //     cid: Slot
    // )
    // {
    //     && cid in n_state.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks 
    //     ==>
    //     (
    //         && cid in n_state.block_consensus_engine_state.block_slashing_db_hist
    //         && n_state.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid].validityPredicate in n_state.block_consensus_engine_state.block_slashing_db_hist[cid] 
    //     )
    // }    

    // predicate inv_current_latest_proposer_duty_match(dv: DVState)    
    // {
    //     forall hn |
    //         && hn in dv.honest_nodes_states.Keys          
    //         ::
    //         inv_current_latest_proposer_duty_match_body_body(
    //             dv.honest_nodes_states[hn]
    //         )                    
    // }           

    // predicate inv_current_latest_proposer_duty_match_body_body(
    //     n_state: DVCState
    // )
    // {
    //     (
    //         && n_state.current_proposer_duty.isPresent()
            
    //     ) ==>
    //     && n_state.latest_proposer_duty.isPresent()
    //     && n_state.current_proposer_duty.safe_get() == n_state.latest_proposer_duty.safe_get()
    // }

    // predicate inv_g_a(dv: DVState)
    // {
    //     forall n | n in dv.honest_nodes_states.Keys :: inv_g_a_body(dv, n)
    // }

    // predicate inv_g_a_body(
    //     dv: DVState, 
    //     n: BLSPubkey
    // )
    // requires n in dv.honest_nodes_states.Keys 
    // {
    //     var n_state := dv.honest_nodes_states[n];
    //     inv_g_a_body_body(dv, n, n_state)
    // }

    // predicate inv_g_a_body_body(
    //     dv: DVState, 
    //     n: BLSPubkey,
    //     n_state: DVCState
    // )
    // {
    //     n_state.latest_proposer_duty.isPresent() ==>
    //         forall an |
    //             && an in dv.sequence_proposer_duties_to_be_served.Values 
    //             && an.node == n 
    //             && an.proposer_duty.slot < n_state.latest_proposer_duty.safe_get().slot
    //         ::
    //             var slot := an.proposer_duty.slot;
    //             && dv.consensus_instances_on_beacon_block[slot].decided_value.isPresent()
    // }         

    // predicate inv_slot_in_future_decided_data_is_correctody_body(
    //     dv: DVState, 
    //     n: BLSPubkey,
    //     n_state: DVCState
    // )
    // {
    //     forall slot |
    //         && slot in n_state.future_proposer_consensus_instances_already_decided
    //         ::
    //         dv.consensus_instances_on_beacon_block[slot].decided_value.isPresent()
    // }    

    // predicate inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
    //     dvc: DVCState,
    //     hn: BLSPubkey,
    //     sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
    //     index_next_proposer_duty_to_be_served: nat
    // )
    // {
    //    forall proposer_duty |
    //         proposer_duty in dvc.all_rcvd_duties
    //         ::
    //         inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_body(                
    //             proposer_duty, 
    //             hn, 
    //             sequence_proposer_duties_to_be_served,
    //             index_next_proposer_duty_to_be_served)
    // }

    // predicate inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_body(        
    //     proposer_duty: ProposerDuty,
    //     hn: BLSPubkey, 
    //     sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
    //     index_next_proposer_duty_to_be_served: nat
    // )
    // {
    //         exists i ::
    //             && 0 <= i
    //             && i < index_next_proposer_duty_to_be_served 
    //             && var duty_and_node := sequence_proposer_duties_to_be_served[i];
    //             && duty_and_node.node == hn
    //             && duty_and_node.proposer_duty == proposer_duty
    // }

    // predicate inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty(dv: DVState)
    // {
    //     forall hn: BLSPubkey | 
    //         is_honest_node(dv, hn) 
    //         ::
    //         && var hn_state := dv.honest_nodes_states[hn];
    //         && inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(                    
    //                 hn_state, 
    //                 hn, 
    //                 dv.sequence_proposer_duties_to_be_served,
    //                 dv.index_next_proposer_duty_to_be_served)
    // }  

    // predicate has_all_slashing_db_proposers_before_slot_s(
    //     db: set<SlashingDBBlock>,
    //     S: set<SlashingDBBlock>,
    //     s: Slot
    // )
    // requires (forall r: SlashingDBBlock :: 
    //                 r in db ==> (exists data: BeaconBlock :: r.signing_root == Some(hash_tree_root(data))))
    // {
    //     && S <= db
    //     && ( forall r | r in db && r !in S :: get_slot_from_slashing_db_proposer(r) >= s )
    //     && ( forall r | r in S :: get_slot_from_slashing_db_proposer(r) < s )
    // }

    // predicate inv_sent_validity_predicate_only_for_slots_stored_in_block_slashing_db_hist(dv: DVState)
    // {
    //     forall hn: BLSPubkey, s: Slot | is_honest_node(dv, hn) ::
    //         && var hn_state := dv.honest_nodes_states[hn];
    //         && ( hn in dv.consensus_instances_on_beacon_block[s].honest_nodes_validity_functions.Keys
    //              ==> 
    //              s in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys)
    // }

    // predicate inv_all_validity_predicates_are_stored_in_block_slashing_db_hist_body(
    //     dv: DVState, 
    //     hn: BLSPubkey,
    //     hn_state: DVCState,
    //     s: Slot,
    //     vp: BeaconBlock -> bool
    // )
    // requires hn in dv.honest_nodes_states.Keys
    // {
    //     (
    //         && var hn_state := dv.honest_nodes_states[hn];
    //         && hn in dv.consensus_instances_on_beacon_block[s].honest_nodes_validity_functions.Keys
    //         && s in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys
    //         && vp in dv.consensus_instances_on_beacon_block[s].honest_nodes_validity_functions[hn]
    //     )
    //         ==>
    //     (
    //         && var hn_state := dv.honest_nodes_states[hn];
    //         && vp in hn_state.block_consensus_engine_state.block_slashing_db_hist[s]   
    //     )             
    // }       
    
    // predicate inv_all_validity_predicates_are_stored_in_block_slashing_db_hist(dv: DVState)
    // {
    //     forall hn: BLSPubkey, s: Slot, vp : BeaconBlock -> bool |
    //         hn in dv.honest_nodes_states.Keys
    //         ::
    //         inv_all_validity_predicates_are_stored_in_block_slashing_db_hist_body(
    //             dv,
    //             hn,
    //             dv.honest_nodes_states[hn],
    //             s,
    //             vp
    //         )
    // }              

    // predicate safety(dv: DVState)
    // {
    //     forall a: Block ::
    //         a in dv.globally_signed_proposers 
    //             ==> 
    //             (
    //                 && var S := dv.globally_signed_proposers - { a };
    //                 && !is_slashable_proposer_data_in_set_of_proposers(S, a.data)
    //             )
    // }

    // predicate inv_queued_proposer_duty_is_dvn_seq_of_proposer_duty1<D(!new, 0)>(ci: ConsensusInstance<D>)
    // {
    //     ci.decided_value.isPresent()
    //     <==> 
    //     is_a_valid_decided_value(ci)            
    // }

    // predicate honest_nodes_with_validityPredicate(consa: ConsensusInstance<BeaconBlock>,  h_nodes_a: set<BLSPubkey>)
    // requires h_nodes_a <= consa.honest_nodes_validity_functions.Keys  
    // requires |h_nodes_a| >= quorum(|consa.all_nodes|) 
    //                                     - (|consa.all_nodes| - |consa.honest_nodes_status.Keys|)
    // requires consa.decided_value.isPresent()
    // {
    //     forall n | n in h_nodes_a 
    //         :: exists vp: BeaconBlock -> bool | vp in consa.honest_nodes_validity_functions[n] 
    //                 :: vp(consa.decided_value.safe_get())
    // }
    
    // predicate inv_exists_honest_node_that_contributed_to_decisions_of_consensus_instances(
    //     dv: DVState, 
    //     a: Block, a': Block, 
    //     m: BLSPubkey,
    //     consa: ConsensusInstance<BeaconBlock>, consa': ConsensusInstance<BeaconBlock>,
    //     h_nodes_a: set<BLSPubkey>, h_nodes_a': set<BLSPubkey>)
    // {
    //     && is_honest_node(dv, m)                
    //     && consa == dv.consensus_instances_on_beacon_block[a.data.slot]
    //     && consa' == dv.consensus_instances_on_beacon_block[a'.data.slot]
    //     && m in consa.honest_nodes_validity_functions.Keys
    //     && m in h_nodes_a
    //     && m in consa'.honest_nodes_validity_functions.Keys                
    //     && m in h_nodes_a'
    //     && consa'.honest_nodes_validity_functions[m] != {}
    //     && is_a_valid_decided_value_according_to_set_of_nodes(consa, h_nodes_a) 
    //     && is_a_valid_decided_value_according_to_set_of_nodes(consa', h_nodes_a') 
    // }

    // predicate inv_unique_rcvd_proposer_duty_per_slot(dv: DVState)
    // {
    //     forall hn: BLSPubkey | 
    //         is_honest_node(dv, hn) 
    //         ::
    //         inv_unique_rcvd_proposer_duty_per_slot_body(dv.honest_nodes_states[hn])
    // }

    // predicate inv_unique_rcvd_proposer_duty_per_slot_body(dvc: DVCState)
    // {
    //     forall d1: ProposerDuty, d2: ProposerDuty | 
    //         && d1 in dvc.all_rcvd_duties
    //         && d2 in dvc.all_rcvd_duties
    //         && d1.slot == d2.slot
    //         ::
    //         d1 == d2
    // }

    // predicate inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_proposer_duty_body(
    //     dv: DVState, 
    //     hn: BLSPubkey, 
    //     s: Slot, 
    //     db: set<SlashingDBBlock>, 
    //     duty: ProposerDuty, 
    //     vp: BeaconBlock -> bool)
    // requires && is_honest_node(dv, hn)
    //          && var hn_state := dv.honest_nodes_states[hn];
    //          && s in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys
    //          && vp in hn_state.block_consensus_engine_state.block_slashing_db_hist[s]
    // {
    //     && var hn_state := dv.honest_nodes_states[hn];
    //     && duty.slot == s
    //     && db in hn_state.block_consensus_engine_state.block_slashing_db_hist[s][vp]
    //     && vp == (ad: BeaconBlock) => ci_decision_ivalilid_beacon_bloc(db, ad, duty)
    // }

    // predicate inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_proposer_duty(dv: DVState)
    // {
    //     forall hn: BLSPubkey, s: Slot, vp: BeaconBlock -> bool | 
    //         && is_honest_node(dv, hn)
    //         && var hn_state := dv.honest_nodes_states[hn];
    //         && s in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys
    //         && vp in hn_state.block_consensus_engine_state.block_slashing_db_hist[s]
    //         ::
    //         exists duty, db ::
    //             && var hn_state := dv.honest_nodes_states[hn];
    //             && inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_proposer_duty_body(dv, hn, s, db, duty, vp)
    // }
    
    // predicate inv_decided_data_has_an_honest_witness_body<D(!new, 0)>(ci: ConsensusInstance) 
    // {
    //     ci.decided_value.isPresent()
    //     ==> 
    //     is_a_valid_decided_value(ci)
    // }
    
    // predicate inv_decided_data_has_an_honest_witness(dv: DVState)
    // {
    //     forall s: Slot ::
    //         && var ci := dv.consensus_instances_on_beacon_block[s];
    //         && inv_decided_data_has_an_honest_witness_body(ci)            
    // }


 
    



    // predicate inv_proposer_duty_in_next_delivery_is_not_lower_than_current_proposer_duty_body(dvc: DVCState, next_duty: ProposerDuty)
    // {
    //     dvc.current_proposer_duty.isPresent()
    //     ==> 
    //     dvc.current_proposer_duty.safe_get().slot <= next_duty.slot        
    // }

    // predicate inv_proposer_duty_in_next_delivery_is_not_lower_than_current_proposer_duty(dv: DVState)
    // {
    //     && var dv_duty_queue := dv.sequence_proposer_duties_to_be_served;
    //     && var dv_index := dv.index_next_proposer_duty_to_be_served;
    //     && var next_duty_and_node := dv_duty_queue[dv_index];
    //     && forall hn: BLSPubkey | 
    //         && hn in dv.honest_nodes_states.Keys
    //         && hn == next_duty_and_node.node 
    //         ::            
    //         && var dvc := dv.honest_nodes_states[hn];
    //         && var next_duty := next_duty_and_node.proposer_duty;
    //         && inv_proposer_duty_in_next_delivery_is_not_lower_than_current_proposer_duty_body(dvc, next_duty)
    // }

    // predicate inv_proposer_duty_in_next_delivery_is_not_lower_than_latest_served_proposer_duty_body(dvc: DVCState, next_duty: ProposerDuty)
    // {
    //     dvc.latest_proposer_duty.isPresent()
    //     ==> 
    //     dvc.latest_proposer_duty.safe_get().slot <= next_duty.slot        
    // }

    // predicate inv_proposer_duty_in_next_delivery_is_not_lower_than_latest_served_proposer_duty(dv: DVState)
    // {
    //     && var dv_duty_queue := dv.sequence_proposer_duties_to_be_served;
    //     && var dv_index := dv.index_next_proposer_duty_to_be_served;
    //     && var next_duty_and_node := dv_duty_queue[dv_index];
    //     && forall hn: BLSPubkey | 
    //         && hn in dv.honest_nodes_states.Keys
    //         && hn == next_duty_and_node.node 
    //         ::            
    //         && var dvc := dv.honest_nodes_states[hn];
    //         && var next_duty := next_duty_and_node.proposer_duty;
    //         && inv_proposer_duty_in_next_delivery_is_not_lower_than_latest_served_proposer_duty_body(dvc, next_duty)
    // }








    // predicate inv_block_shares_to_broadcast_is_a_subset_of_all_messages_sent_single_node(
    //     dv: DVState,
    //     n: BLSPubkey
    // )
    // requires n in dv.honest_nodes_states.Keys 
    // {
    //     dv.honest_nodes_states[n].block_shares_to_broadcast.Values <= dv.block_share_network.allMessagesSent
    // }

    // predicate inv_block_shares_to_broadcast_is_a_subset_of_all_messages_sent(
    //     dv: DVState
    // )
    // {
    //     forall n |
    //         n in dv.honest_nodes_states.Keys 
    //         ::
    //     inv_block_shares_to_broadcast_is_a_subset_of_all_messages_sent_single_node(dv, n)
    // }    


    // predicate inv_active_consensus_instances_implied_the_delivery_of_proposer_duties_body(hn_state: DVCState, s: Slot)
    // requires s in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys
    // {
    //     exists duty: ProposerDuty :: 
    //                 && duty in hn_state.all_rcvd_duties
    //                 && duty.slot == s
    // }


    // predicate inv_active_consensus_instances_implied_the_delivery_of_proposer_duties(dv: DVState)
    // {
    //     forall hn: BLSPubkey, s: Slot ::
    //         ( && is_honest_node(dv, hn) 
    //           && var hn_state := dv.honest_nodes_states[hn];
    //           && s in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys
    //         )
    //         ==>
    //         inv_active_consensus_instances_implied_the_delivery_of_proposer_duties_body(dv.honest_nodes_states[hn], s)                
    // }

    // predicate inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(hn_state: DVCState)    
    // {
    //     forall k: Slot | k in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys ::
    //         exists duty: ProposerDuty :: 
    //                 && duty in hn_state.all_rcvd_duties
    //                 && duty.slot == k
    // }

    // predicate inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties(dv: DVState)
    // {
    //     forall hn: BLSPubkey | is_honest_node(dv, hn) ::
    //         && var hn_state := dv.honest_nodes_states[hn];            
    //         && inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(hn_state)       
    // }

    // predicate inv_exists_db_in_block_slashing_db_hist_and_duty_for_every_validity_predicate_body_ces(ces: ConsensusEngineState)
    // {
    //     forall s: Slot, vp: BeaconBlock -> bool |
    //             ( && s in ces.block_slashing_db_hist.Keys
    //               && vp in ces.block_slashing_db_hist[s]
    //             )
    //             :: 
    //             ( exists db: set<SlashingDBBlock>, duty: ProposerDuty ::
    //                     && duty.slot == s
    //                     && db in ces.block_slashing_db_hist[s][vp]
    //                     && vp == (ad: BeaconBlock) => ci_decision_ivalilid_beacon_bloc(db, ad, duty)
    //             )
    // }

    // predicate inv_exists_db_in_block_slashing_db_hist_and_duty_for_every_validity_predicate_body(hn_state: DVCState)
    // {
    //     forall s: Slot, vp: BeaconBlock -> bool |
    //             ( && s in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys
    //               && vp in hn_state.block_consensus_engine_state.block_slashing_db_hist[s]
    //             )
    //             :: 
    //             ( exists db: set<SlashingDBBlock>, duty: ProposerDuty ::
    //                     && duty.slot == s
    //                     && db in hn_state.block_consensus_engine_state.block_slashing_db_hist[s][vp]
    //                     && vp == (ad: BeaconBlock) => ci_decision_ivalilid_beacon_bloc(db, ad, duty)
    //             )
    // }

    // predicate inv_exists_db_in_block_slashing_db_hist_and_duty_for_every_validity_predicate(dv: DVState)
    // {
    //     forall hn: BLSPubkey | is_honest_node(dv, hn) ::
    //         && var dvc := dv.honest_nodes_states[hn];
    //         && inv_exists_db_in_block_slashing_db_hist_and_duty_for_every_validity_predicate_body(dvc)
    // }

    // predicate inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(hn_state: DVCState)
    // {
    //     forall k: Slot |
    //         k in hn_state.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys ::
    //             && var ci := hn_state.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[k];
    //             && var vp: BeaconBlock -> bool := ci.validityPredicate;
    //             && k in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys 
    //             && vp in hn_state.block_consensus_engine_state.block_slashing_db_hist[k].Keys             
    // }

    // predicate inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k(dv: DVState)
    // {
    //     forall hn: BLSPubkey | is_honest_node(dv, hn) ::
    //         && var dvc := dv.honest_nodes_states[hn];
    //         && inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(dvc)
    // }

    // predicate inv_monotonic_block_slashing_db_body(dvc: DVCState, dvc': DVCState)
    // {
    //     dvc.block_slashing_db <= dvc'.block_slashing_db
    // }

    // predicate inv_monotonic_block_slashing_db(dv: DVState, event: DV.Event, dv': DVState)    
    // {
    //     forall hn: BLSPubkey | is_honest_node(dv, hn) ::
    //         && hn in dv'.honest_nodes_states
    //         && var dvc := dv.honest_nodes_states[hn];
    //         && var dvc' := dv'.honest_nodes_states[hn];
    //         && inv_monotonic_block_slashing_db_body(dvc, dvc')
    // }

    // predicate inv_every_db_in_block_slashing_db_hist_is_subset_of_block_slashing_db_body_ces(ces: ConsensusEngineState, block_slashing_db: set<SlashingDBBlock>)
    // {
    //     forall s: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> |
    //             ( && s in ces.block_slashing_db_hist.Keys
    //               && vp in ces.block_slashing_db_hist[s]
    //               && db in ces.block_slashing_db_hist[s][vp]
    //             )
    //             :: 
    //             db <= block_slashing_db
    // }

    // predicate inv_every_db_in_block_slashing_db_hist_is_subset_of_block_slashing_db_body(hn_state: DVCState)
    // {
    //     forall s: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> |
    //             ( && s in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys
    //               && vp in hn_state.block_consensus_engine_state.block_slashing_db_hist[s]
    //               && db in hn_state.block_consensus_engine_state.block_slashing_db_hist[s][vp]
    //             )
    //             :: 
    //             db <= hn_state.block_slashing_db
    // }

    // predicate inv_every_db_in_block_slashing_db_hist_is_subset_of_block_slashing_db(dv: DVState)
    // {
    //     forall hn: BLSPubkey | is_honest_node(dv, hn) ::
    //         && var dvc := dv.honest_nodes_states[hn];
    //         && inv_every_db_in_block_slashing_db_hist_is_subset_of_block_slashing_db_body(dvc)
    // }

    // predicate inv_monotonic_block_slashing_db_hist_body(dvc: DVCState, dvc': DVCState)
    // {        
    //     dvc.block_consensus_engine_state.block_slashing_db_hist.Keys
    //     <= 
    //     dvc'.block_consensus_engine_state.block_slashing_db_hist.Keys
    // }

    // predicate inv_monotonic_block_slashing_db_hist(dv: DVState, event: DV.Event, dv': DVState)    
    // {
    //     forall hn: BLSPubkey | is_honest_node(dv, hn) ::
    //         && hn in dv'.honest_nodes_states
    //         && var dvc := dv.honest_nodes_states[hn];
    //         && var dvc' := dv'.honest_nodes_states[hn];
    //         && inv_monotonic_block_slashing_db_hist_body(dvc, dvc')
    // }

    // predicate prop_monotonic_set_of_in_transit_messages(dv: DVState, dv': DVState)
    // {
    //     && dv.block_share_network.allMessagesSent <= dv'.block_share_network.allMessagesSent
    // }
     
   
    // predicate inv_active_proposern_consensus_instances_are_tracked_in_block_slashing_db_hist_body(dvc: DVCState)
    // {
    //     dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys 
    //     <= 
    //     dvc.block_consensus_engine_state.block_slashing_db_hist.Keys
    // } 

    // predicate inv_active_proposern_consensus_instances_are_tracked_in_block_slashing_db_hist(dv: DVState)
    // {
    //     forall hn | hn in dv.honest_nodes_states.Keys ::
    //         && var dvc := dv.honest_nodes_states[hn];
    //         && inv_active_proposern_consensus_instances_are_tracked_in_block_slashing_db_hist_body(dvc)
    // } 

    // predicate inv_construct_complete_signed_signature_assumptions_helper(dv: DVState)
    // {
    //     construct_complete_signed_signature_assumptions_helper(
    //         dv.construct_complete_signed_block,
    //         dv.dv_pubkey,
    //         dv.all_nodes)
    // }



    // predicate inv_rcvd_proposern_shares_are_from_sent_messages_body(
    //     dv: DVState,
    //     dvc: DVCState
    // )
    // {
    //     var rcvd_block_shares := dvc.rcvd_block_shares;

    //     forall i, j |
    //         && i in rcvd_block_shares.Keys 
    //         && j in rcvd_block_shares[i]
    //         ::
    //         rcvd_block_shares[i][j] <= dv.block_share_network.allMessagesSent
    // }    

    // predicate inv_rcvd_proposern_shares_are_from_sent_messages(
    //     dv: DVState    
    // )
    // {
    //     forall n | n in dv.honest_nodes_states ::
    //         && var dvc := dv.honest_nodes_states[n];
    //         && inv_rcvd_proposern_shares_are_from_sent_messages_body(dv, dvc)
    // } 


    // predicate inv_block_shares_to_broadcast_are_sent_messages_body(
    //     dv: DVState,
    //     dvc: DVCState
    // )    
    // {
    //     dvc.block_shares_to_broadcast.Values <= dv.block_share_network.allMessagesSent
    // }

    // predicate inv_block_shares_to_broadcast_are_sent_messages(
    //     dv: DVState
    // )
    // {
    //     forall n | n in dv.honest_nodes_states.Keys ::
    //         && var dvc := dv.honest_nodes_states[n];
    //         && inv_block_shares_to_broadcast_are_sent_messages_body(dv, dvc)
    // }

    // predicate inv39(
    //     dv: DVState,        
    //     dv': DVState
    // )       
    // {
    //     dv.block_share_network.allMessagesSent <= dv'.block_share_network.allMessagesSent
    // }

    
    // predicate inv_slots_for_sent_validity_predicate_are_stored_in_block_slashing_db_hist_body(
    //     dv: DVState, 
    //     hn: BLSPubkey,
    //     hn_state: DVCState,
    //     s: Slot
    // )
    // {
    //     hn in dv.consensus_instances_on_beacon_block[s].honest_nodes_validity_functions.Keys
    //     ==> s in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys
    // }

    // predicate inv_slots_for_sent_validity_predicate_are_stored_in_block_slashing_db_hist(dv: DVState)
    // {
    //     forall hn: BLSPubkey, s: Slot |
    //         hn in dv.honest_nodes_states
    //         :: 
    //         inv_slots_for_sent_validity_predicate_are_stored_in_block_slashing_db_hist_body(dv, hn, dv.honest_nodes_states[hn], s)        
    // } 

    // predicate inv_no_active_consensus_instance_before_receiving_proposer_duty_body(dvc: DVCState)
    // {
    //     !dvc.latest_proposer_duty.isPresent()
    //     ==> dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys == {}
    // }

    // predicate inv_no_active_consensus_instance_before_receiving_proposer_duty(dv: DVState)
    // {
    //     forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
    //         && var dvc := dv.honest_nodes_states[hn];
    //         && inv_no_active_consensus_instance_before_receiving_proposer_duty_body(dvc)
    // }

    // predicate inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_proposer_duty_body(dvc: DVCState)
    // {
    //     dvc.latest_proposer_duty.isPresent()
    //     ==> ( forall k: Slot | k in dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys 
    //             ::
    //             k <= dvc.latest_proposer_duty.safe_get().slot
    //         )
    // }

    // predicate inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_proposer_duty(dv: DVState)
    // {
    //     forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
    //         && var dvc := dv.honest_nodes_states[hn];
    //         && inv_slot_of_active_consensus_instance_is_lower_than_slot_of_latest_served_proposer_duty_body(dvc)
    // }

    // predicate inv_consensus_instances_are_isConditionForSafetyTrue(dv: DVState)
    // {
    //     forall slot: Slot | slot in dv.consensus_instances_on_beacon_block.Keys  ::
    //                 isConditionForSafetyTrue(dv.consensus_instances_on_beacon_block[slot])                    
    // }

    // predicate pred_last_proposer_duty_is_delivering_to_given_honest_node(
    //     proposer_duty: ProposerDuty,
    //     dv: DVState,
    //     n: BLSPubkey,
    //     index_next_proposer_duty_to_be_served: nat
    // )
    // {
    //     && 0 < index_next_proposer_duty_to_be_served 
    //     && var i := index_next_proposer_duty_to_be_served - 1;
    //     && var an := dv.sequence_proposer_duties_to_be_served[i];
    //     && an.proposer_duty == proposer_duty
    //     && an.node == n
    // }

    // predicate inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(dvc: DVCState)
    // {
    //     !dvc.latest_proposer_duty.isPresent()
    //     <==> 
    //     dvc.all_rcvd_duties == {}
    // }

    // predicate inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties(dv: DVState)
    // {
    //     forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
    //         inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(dv.honest_nodes_states[hn])
    // }

    // predicate inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(dvc: DVCState)
    // {
    //     dvc.latest_proposer_duty.isPresent()
    //     ==>
    //     ( forall proposer_duty | proposer_duty in dvc.all_rcvd_duties ::
    //         proposer_duty.slot <= dvc.latest_proposer_duty.safe_get().slot
    //     )
    // }

    // predicate inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty(dv: DVState)
    // {
    //     forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
    //         &&  var dvc := dv.honest_nodes_states[hn];
    //         &&  inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(dvc)
    // }

    // predicate inv_data_of_all_created_proposers_is_set_of_decided_values(dv: DVState)
    // {
    //     forall a | a in dv.all_proposers_created ::
    //             && var consa := dv.consensus_instances_on_beacon_block[a.data.slot];
    //             && consa.decided_value.isPresent() 
    //             && a.data == consa.decided_value.safe_get() 
    // }

    // predicate inv_one_honest_dvc_is_required_to_pass_signer_threshold(
    //     dv: DVState,
    //     signers: set<BLSPubkey>,
    //     block_shares: set<BlockShare>,
    //     signing_root: Root
    // )
    // {
    //     (
    //         && signer_threshold(signers, block_shares, signing_root)
    //         && signers <= dv.all_nodes
    //     )
    //     ==>
    //     (
    //         exists h_node ::
    //             && h_node in signers
    //             && is_honest_node(dv, h_node)
    //     )
    // }

    // predicate inv_all_created_proposers_are_valid(dv: DVState)
    // {
    //     forall a | a in dv.all_proposers_created ::
    //             is_valid_proposer(a, dv.dv_pubkey)
    // }

    // predicate inv_outputs_proposers_submited_are_valid(
    //     outputs: Outputs,
    //     dv_pubkey: BLSPubkey)
    // {
    //     forall submitted_block | submitted_block in outputs.proposers_submitted ::
    //         is_valid_proposer(submitted_block, dv_pubkey)
    // }

    // predicate pred_slashing_db_proposer_in_two_dbs(
    //     sdba: SlashingDBBlock,
    //     db1: set<SlashingDBBlock>,
    //     db2: set<SlashingDBBlock>
    // )
    // {
    //     && sdba in db1
    //     && sdba in db2
    // }

    // predicate inv_slashing_db_proposer_in_db_for_low_slot_is_in_db_for_high_slot_body_helper(
    //             set_db:  set<set<SlashingDBBlock>>,
    //             set_db':  set<set<SlashingDBBlock>>
    // )
    // {
    //     forall db, db', sdba |
    //         && db in set_db
    //         && db' in set_db'
    //         ::
    //         (   sdba in db
    //             ==>
    //             sdba in db'
    //         )
    // }

    // predicate inv_slashing_db_proposer_in_db_for_low_slot_is_in_db_for_high_slot_body_body(
    //     db_hist_on_slot: map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>,
    //     db_hist_on_slot': map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>
    // )
    // {
    //     forall vp, vp' |
    //         && vp in db_hist_on_slot.Keys
    //         && vp' in db_hist_on_slot'.Keys 
    //         ::
    //         inv_slashing_db_proposer_in_db_for_low_slot_is_in_db_for_high_slot_body_helper(
    //             db_hist_on_slot[vp],
    //             db_hist_on_slot'[vp']
    //         )
             
    // }

    // predicate inv_slashing_db_proposer_in_db_for_low_slot_is_in_db_for_high_slot_body(
    //     dvc: DVCState
    // )
    // {
    //     forall slot:Slot, slot': Slot | 
    //         && slot in dvc.block_consensus_engine_state.block_slashing_db_hist.Keys
    //         && slot' in dvc.block_consensus_engine_state.block_slashing_db_hist.Keys 
    //         && slot < slot'
    //         ::
    //         inv_slashing_db_proposer_in_db_for_low_slot_is_in_db_for_high_slot_body_body(
    //              dvc.block_consensus_engine_state.block_slashing_db_hist[slot], 
    //              dvc.block_consensus_engine_state.block_slashing_db_hist[slot']
    //         )
    // }

    // predicate inv_slashing_db_proposer_in_db_for_low_slot_is_in_db_for_high_slot(
    //     dv: DVState
    // )
    // {
    //     forall hn: BLSPubkey | is_honest_node(dv, hn) ::
    //         inv_slashing_db_proposer_in_db_for_low_slot_is_in_db_for_high_slot_body(dv.honest_nodes_states[hn])
        
    // }

    // predicate pred_verify_owner_of_block_share_with_bls_signature(
    //     rs_pubkey: BLSPubkey,
    //     block_share: SignedBeaconBlock
    // )
    // {
    //     && var decided_beacon_block := block_share.block;
    //     && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_beacon_block.target.epoch));
    //     && var proposer_signing_root := compute_proposer_signing_root(decided_beacon_block, fork_version);
    //     && verify_bls_signature(proposer_signing_root, block_share.signature, rs_pubkey)
    // }

    // predicate pred_is_owner_of_one_proposerestaion_share_in_set_of_shares(
    //     rs_pubkey: BLSPubkey,
    //     block_shares: set<BlockShare>
    // )
    // {
    //     exists share | share in block_shares ::
    //         pred_verify_owner_of_block_share_with_bls_signature(rs_pubkey, share)
    // }

    // predicate pred_proposer_is_created_based_on_sent_block_shares(
    //     dv: DVState,
    //     proposer: Block,
    //     block_shares: set<BlockShare>
    // )
    // {
    //     && block_shares <= dv.block_share_network.allMessagesSent
    //     && var constructed_sig := dv.construct_complete_signed_block(block_shares);
    //     && constructed_sig.isPresent()
    //     && constructed_sig.safe_get() == proposer.signature
    //     && all_block_shares_have_the_same_data(block_shares, proposer.data)
    // }

    // predicate inv_exists_honest_node_that_contributed_to_creation_of_two_submitted_blocks_body(
    //     dv: DVState,
    //     a: Block, 
    //     a': Block
    // )
    // {
    //     exists hn: BLSPubkey, block_shares: set<BlockShare>, block_shares': set<BlockShare> ::
    //         && is_honest_node(dv, hn)
    //         && var rs_pubkey: BLSPubkey := dv.honest_nodes_states[hn].rs.pubkey;
    //         && pred_proposer_is_created_based_on_sent_block_shares(dv, a, block_shares)            
    //         && pred_is_owner_of_one_proposerestaion_share_in_set_of_shares(rs_pubkey, block_shares)
    //         && pred_proposer_is_created_based_on_sent_block_shares(dv, a', block_shares')
    //         && pred_is_owner_of_one_proposerestaion_share_in_set_of_shares(rs_pubkey, block_shares')
    // }

    // predicate inv_exists_honest_node_that_contributed_to_creation_of_two_submitted_blocks(
    //     dv: DVState)
    // {
    //     forall a: Block, a': Block |
    //         && a in dv.all_proposers_created
    //         && a' in dv.all_proposers_created
    //         ::
    //         inv_exists_honest_node_that_contributed_to_creation_of_two_submitted_blocks_body(dv, a, a')
    // }
    
    // predicate inv_if_honest_node_sends_block_share_it_receives_proposer_data_before_body(
    //     dvc: DVCState,
    //     block_share: SignedBeaconBlock
    // )
    // {
    //     && var proposer_data: BeaconBlock := block_share.block;
    //     && var slot: Slot := proposer_data.slot;
    //     && var slashing_db_proposer := SlashingDBBlock(
    //                                         source_epoch := proposer_data.source.epoch,
    //                                         target_epoch := proposer_data.target.epoch,
    //                                         signing_root := Some(hash_tree_root(proposer_data)));
    //     && slashing_db_proposer in dvc.block_slashing_db
    //     && exists proposer_duty: ProposerDuty, vp: BeaconBlock -> bool :: 
    //             (   && proposer_duty in dvc.all_rcvd_duties
    //                 && slot in dvc.block_consensus_engine_state.block_slashing_db_hist.Keys
    //                 && vp in dvc.block_consensus_engine_state.block_slashing_db_hist[slot].Keys
    //                 && vp(proposer_data)
    //             )
    // }

    // predicate inv_if_honest_node_sends_block_share_it_receives_proposer_data_before(dv: DVState)
    // {
    //     forall hn, block_share |
    //         && is_honest_node(dv, hn)
    //         && block_share in dv.block_share_network.allMessagesSent
    //         && var rs_pubkey: BLSPubkey := dv.honest_nodes_states[hn].rs.pubkey;
    //         && pred_verify_owner_of_block_share_with_bls_signature(rs_pubkey, block_share)
    //         ::
    //         && var dvc := dv.honest_nodes_states[hn];
    //         && inv_if_honest_node_sends_block_share_it_receives_proposer_data_before_body(dvc, block_share)
    // }

    // predicate inv_data_of_sent_block_shares_is_known_body(
    //     dvc: DVCState,
    //     block_share: SignedBeaconBlock
    // )
    // {
    //     && var proposer_data: BeaconBlock := block_share.block;
    //     && var slot: Slot := proposer_data.slot;
    //     && var slashing_db_proposer := SlashingDBBlock(
    //                                         source_epoch := proposer_data.source.epoch,
    //                                         target_epoch := proposer_data.target.epoch,
    //                                         signing_root := Some(hash_tree_root(proposer_data)));
    //     && slashing_db_proposer in dvc.block_slashing_db
    //     && exists proposer_duty: ProposerDuty, vp: BeaconBlock -> bool :: 
    //             (   && proposer_duty in dvc.all_rcvd_duties
    //                 && slot in dvc.block_consensus_engine_state.block_slashing_db_hist.Keys
    //                 && vp in dvc.block_consensus_engine_state.block_slashing_db_hist[slot].Keys
    //                 && vp(proposer_data)
    //             )
    // }

    // predicate inv_outputs_block_shares_sent_is_tracked_in_block_slashing_db_body(
    //     dvc: DVCState, 
    //     block_share: SignedBeaconBlock
    // )
    // {
    //     && var proposer_data: BeaconBlock := block_share.block;
    //     && var slashing_db_proposer := construct_SlashingDBBlock_from_proposer_data(proposer_data);
    //     && slashing_db_proposer in dvc.block_slashing_db  
    //     && var rs_pubkey: BLSPubkey := dvc.rs.pubkey;    
    //     && pred_verify_owner_of_block_share_with_bls_signature(rs_pubkey, block_share)
    // }   

    // predicate inv_outputs_block_shares_sent_is_tracked_in_block_slashing_db(
    //     outputs: Outputs,
    //     dvc: DVCState)
    // {
    //     forall block_share: SignedBeaconBlock | 
    //         block_share in getMessagesFromMessagesWithRecipient(outputs.block_shares_sent) 
    //         ::
    //         inv_outputs_block_shares_sent_is_tracked_in_block_slashing_db_body(dvc, block_share)
    // } 

    // predicate inv_block_shares_to_broadcast_is_tracked_in_block_slashing_db_body(
    //     dvc: DVCState
    // )
    // {
    //     forall slot: Slot | 
    //         slot in dvc.block_shares_to_broadcast.Keys
    //         ::
    //         && var block_share: SignedBeaconBlock := dvc.block_shares_to_broadcast[slot];
    //         && var proposer_data: BeaconBlock := block_share.block;
    //         && var slashing_db_proposer := construct_SlashingDBBlock_from_proposer_data(proposer_data);
    //         && slashing_db_proposer in dvc.block_slashing_db  
    //         && var rs_pubkey: BLSPubkey := dvc.rs.pubkey;    
    //         && pred_verify_owner_of_block_share_with_bls_signature(rs_pubkey, block_share)
    // }   

    // predicate inv_block_shares_to_broadcast_is_tracked_in_block_slashing_db(
    //     dv: DVState)
    // {
    //     forall hn: BLSPubkey | 
    //         is_honest_node(dv, hn)
    //         ::
    //         inv_block_shares_to_broadcast_is_tracked_in_block_slashing_db_body(dv.honest_nodes_states[hn])
    // } 

    // predicate inv_block_of_block_shares_is_known_body(
    //     dvc: DVCState,
    //     block_share: SignedBeaconBlock
    // )
    // {
    //     && var proposer_data := block_share.block;
    //     && var slashing_db_proposer := construct_SlashingDBBlock_from_proposer_data(proposer_data);
    //     && slashing_db_proposer in dvc.block_slashing_db     
    // }

    // predicate inv_block_of_block_shares_is_known(
    //     dv: DVState
    // )
    // {
    //     forall hn: BLSPubkey, block_share: SignedBeaconBlock | 
    //         && is_honest_node(dv, hn)
    //         && block_share in dv.block_share_network.allMessagesSent 
    //         && var dvc: DVCState := dv.honest_nodes_states[hn];
    //         && var rs_pubkey: BLSPubkey := dvc.rs.pubkey;
    //         && pred_verify_owner_of_block_share_with_bls_signature(rs_pubkey, block_share)
    //         ::
    //         && var dvc: DVCState := dv.honest_nodes_states[hn];
    //         && inv_block_of_block_shares_is_known_body(dvc, block_share)            
    // }

    // predicate inv_proposer_is_created_with_shares_from_quorum_body_signers_helper(
    //     block_shares: set<BlockShare>,
    //     dvc: DVCState
    // )
    // {
    //     exists block_share: SignedBeaconBlock ::
    //         && block_share in block_shares
    //         && var rs_pubkey := dvc.rs.pubkey;
    //         && pred_verify_owner_of_block_share_with_bls_signature(rs_pubkey, block_share)
    // }

    // predicate inv_proposer_is_created_with_shares_from_quorum_body_signers(
    //     dv: DVState,
    //     block_shares: set<BlockShare>,
    //     dvc_signer_pubkeys: set<BLSPubkey>
    // )
    // {
    //     forall key: BLSPubkey | key in dvc_signer_pubkeys ::
    //         key in dv.honest_nodes_states.Keys
    //         ==>
    //         inv_proposer_is_created_with_shares_from_quorum_body_signers_helper(
    //                 block_shares,
    //                 dv.honest_nodes_states[key]
    //             )        
    // }

    // predicate inv_proposer_is_created_with_shares_from_quorum_body_helper(
    //     dv: DVState, 
    //     proposer: Block,
    //     block_shares: set<BlockShare>, 
    //     signers: set<BLSPubkey>
    // )
    // {
    //     && block_shares <= dv.block_share_network.allMessagesSent
    //     && var constructed_sig := dv.construct_complete_signed_block(block_shares);
    //     && constructed_sig.isPresent()
    //     && constructed_sig.safe_get() == proposer.signature
    //     && all_block_shares_have_the_same_data(block_shares, proposer.data)
    //     && signers <= dv.all_nodes
    //     && inv_proposer_is_created_with_shares_from_quorum_body_signers(dv, block_shares, signers)
    //     && |signers| >= quorum(|dv.all_nodes|)
    // }

    // predicate inv_proposer_is_created_with_shares_from_quorum_body(
    //     dv: DVState, 
    //     proposer: Block        
    // )
    // {
    //     exists block_shares, dvc_signer_pubkeys :: 
    //             && block_shares <= dv.block_share_network.allMessagesSent
    //             && var constructed_sig := dv.construct_complete_signed_block(block_shares);
    //             && constructed_sig.isPresent()
    //             && constructed_sig.safe_get() == proposer.signature
    //             && all_block_shares_have_the_same_data(block_shares, proposer.data)
    //             && dvc_signer_pubkeys <= dv.all_nodes
    //             && inv_proposer_is_created_with_shares_from_quorum_body_signers(dv, block_shares, dvc_signer_pubkeys)
    //             && |dvc_signer_pubkeys| >= quorum(|dv.all_nodes|)
    // }

    // predicate inv_proposer_is_created_with_shares_from_quorum(dv: DVState)
    // {
    //     forall proposer: Block | proposer in dv.all_proposers_created ::
    //             inv_proposer_is_created_with_shares_from_quorum_body(dv, proposer)
    // }

    // predicate inv_proposer_is_created_with_shares_from_quorum_rs_signers_body(
    //     block_shares: set<BlockShare>,
    //     rs_signer_pubkey: BLSPubkey
    // )
    // {
    //     exists block_share: SignedBeaconBlock ::
    //         && block_share in block_shares
    //         && pred_verify_owner_of_block_share_with_bls_signature(rs_signer_pubkey, block_share)
    // }

    // predicate inv_proposer_is_created_with_shares_from_quorum_rs_signers(
    //     block_shares: set<BlockShare>,
    //     rs_signer_pubkeys: set<BLSPubkey>
    // )
    // {
    //     forall key: BLSPubkey | key in rs_signer_pubkeys ::
    //             inv_proposer_is_created_with_shares_from_quorum_rs_signers_body(
    //                 block_shares,
    //                 key
    //             )        
    // }

    // predicate inv_outputs_proposers_submited_is_created_with_shares_from_quorum_body(
    //     dvc: DVCState, 
    //     proposer: Block
    // )
    // {
    //     && proposer.data.slot in dvc.rcvd_block_shares.Keys
    //     && exists block_shares, rs_signer_pubkeys, k ::          
    //             && k in dvc.rcvd_block_shares[proposer.data.slot].Keys
    //             && block_shares <= dvc.rcvd_block_shares[proposer.data.slot][k]
    //             && var constructed_sig := dvc.construct_complete_signed_block(block_shares);
    //             && constructed_sig.isPresent()
    //             && constructed_sig.safe_get() == proposer.signature
    //             && all_block_shares_have_the_same_data(block_shares, proposer.data)
    //             && inv_proposer_is_created_with_shares_from_quorum_rs_signers(block_shares, rs_signer_pubkeys)
    //             && |rs_signer_pubkeys| >= quorum(|dvc.peers|)
    //             && rs_signer_pubkeys <= dvc.peers
    // }   

    // predicate inv_outputs_proposers_submited_is_created_with_shares_from_quorum(
    //     outputs: Outputs,
    //     dvc: DVCState)
    // {
    //     forall submitted_block | submitted_block in outputs.proposers_submitted ::
    //         inv_outputs_proposers_submited_is_created_with_shares_from_quorum_body(dvc, submitted_block)
    // } 

    // predicate pred_intersection_of_honest_nodes_in_two_quorum_contains_an_honest_node(
    //     dv: DVState,
    //     h_nodes_1: set<BLSPubkey>,
    //     h_nodes_2: set<BLSPubkey>
    // )
    // {
    //     && h_nodes_1 <= dv.honest_nodes_states.Keys
    //     && h_nodes_2 <= dv.honest_nodes_states.Keys
    //     && |h_nodes_1| >= quorum(|dv.all_nodes|) - |dv.adversary.nodes|
    //     && |h_nodes_2| >= quorum(|dv.all_nodes|) - |dv.adversary.nodes|
    //     ==>
    //     exists hn ::
    //         && hn in dv.honest_nodes_states.Keys
    //         && hn in h_nodes_1
    //         && hn in h_nodes_2
    // }

    // predicate inv_db_of_vp_contains_all_proposer_data_of_sent_block_shares_for_lower_slots_body(
    //     dv: DVState,
    //     hn: BLSPubkey,
    //     slot: Slot, 
    //     vp: BeaconBlock -> bool, 
    //     db: set<SlashingDBBlock>
    // )
    // {
    //     forall block_share: SignedBeaconBlock | 
    //         && block_share in dv.block_share_network.allMessagesSent
    //         && is_honest_node(dv, hn)
    //         && var dvc := dv.honest_nodes_states[hn];
    //         && var rs_pubkey := dvc.rs.pubkey;
    //         && pred_verify_owner_of_block_share_with_bls_signature(rs_pubkey, block_share)
    //         && block_share.block.slot < slot
    //         ::
    //         && var proposer_data := block_share.block;
    //         && var slashing_db_proposer := SlashingDBBlock(
    //                                         source_epoch := proposer_data.source.epoch,
    //                                         target_epoch := proposer_data.target.epoch,
    //                                         signing_root := Some(hash_tree_root(proposer_data)));
    //         && slashing_db_proposer in db
    // }

    // predicate inv_db_of_vp_contains_all_proposer_data_of_sent_block_shares_for_lower_slots(dv: DVState)
    // {
    //     forall hn: BLSPubkey, slot: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> | 
    //         && is_honest_node(dv, hn) 
    //         && var dvc := dv.honest_nodes_states[hn];
    //         && slot in dvc.block_consensus_engine_state.block_slashing_db_hist
    //         && vp in dvc.block_consensus_engine_state.block_slashing_db_hist[slot]
    //         && db in dvc.block_consensus_engine_state.block_slashing_db_hist[slot][vp]
    //         :: 
    //         inv_db_of_vp_contains_all_proposer_data_of_sent_block_shares_for_lower_slots_body(
    //             dv,
    //             hn,
    //             slot,
    //             vp,
    //             db)
    // }

    // predicate inv_db_of_vp_contains_all_proposer_data_of_sent_block_shares_for_lower_slots_body_dvc(
    //     allMessagesSent: set<BlockShare>,
    //     rs_pubkey: BLSPubkey,
    //     slot: Slot, 
    //     vp: BeaconBlock -> bool, 
    //     db: set<SlashingDBBlock>
    // )
    // {
    //     forall block_share: SignedBeaconBlock | 
    //         && block_share in allMessagesSent
    //         && pred_verify_owner_of_block_share_with_bls_signature(rs_pubkey, block_share)
    //         && block_share.block.slot < slot
    //         ::
    //         && var proposer_data := block_share.block;
    //         && var slashing_db_proposer := SlashingDBBlock(
    //                                         source_epoch := proposer_data.source.epoch,
    //                                         target_epoch := proposer_data.target.epoch,
    //                                         signing_root := Some(hash_tree_root(proposer_data)));
    //         && slashing_db_proposer in db
    // }

    // predicate inv_db_of_vp_contains_all_proposer_data_of_sent_block_shares_for_lower_slots_dvc(
    //     allMessagesSent: set<BlockShare>,
    //     dvc: DVCState        
    // )
    // {
    //     forall slot: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> | 
    //         && slot in dvc.block_consensus_engine_state.block_slashing_db_hist
    //         && vp in dvc.block_consensus_engine_state.block_slashing_db_hist[slot]
    //         && db in dvc.block_consensus_engine_state.block_slashing_db_hist[slot][vp]
    //         :: 
    //         inv_db_of_vp_contains_all_proposer_data_of_sent_block_shares_for_lower_slots_body_dvc(
    //             allMessagesSent,
    //             dvc.rs.pubkey,
    //             slot,
    //             vp,
    //             db
    //         )
    // }

    // predicate inv_unchanged_dvc_rs_pubkey(dv: DVState)
    // {
    //     forall hn: BLSPubkey | is_honest_node(dv, hn) ::
    //         && var dvc: DVCState := dv.honest_nodes_states[hn];
    //         && dvc.rs.pubkey == hn
    // }

    // predicate inv_honest_nodes_are_not_owner_of_block_shares_from_adversary_body(
    //     dv: DVState, 
    //     block_share: SignedBeaconBlock
    // )
    // {
    //     forall hn: BLSPubkey | is_honest_node(dv, hn) :: 
    //         !pred_verify_owner_of_block_share_with_bls_signature(hn, block_share)
    // }

    // predicate inv_honest_nodes_are_not_owner_of_block_shares_from_adversary(dv: DVState)
    // {
    //     forall byz_node: BLSPubkey, block_share: SignedBeaconBlock | 
    //         && byz_node in dv.adversary.nodes 
    //         && block_share in dv.block_share_network.allMessagesSent
    //         && pred_verify_owner_of_block_share_with_bls_signature(byz_node, block_share)
    //         ::
    //         inv_honest_nodes_are_not_owner_of_block_shares_from_adversary_body(dv, block_share)
    // }
}