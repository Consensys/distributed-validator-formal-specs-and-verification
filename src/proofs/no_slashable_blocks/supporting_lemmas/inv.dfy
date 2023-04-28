include "../../../common/commons.dfy"

include "../../../specs/consensus/block_consensus.dfy"
include "../../../specs/network/network.dfy"
include "../../../specs/dv/dv_block_proposer.dfy"
include "../common/dvc_block_proposer_instrumented.dfy"
include "../../common/helper_sets_lemmas.dfy"
include "../common/block_dvc_spec_axioms.dfy"



module Block_Inv_With_Empty_Initial_Block_Slashing_DB
{
    import opened Types 
    import opened CommonFunctions
    
    import opened Block_Consensus_Spec
    import opened NetworkSpec
    import opened DVC_Block_Proposer_Spec_Instr
    import opened DV_Block_Proposer_Spec
    import opened Helper_Sets_Lemmas
    import opened DVC_Block_Proposer_Spec_Axioms


    predicate is_an_honest_node(s: DVState, n: BLSPubkey)
    {
        && n in s.honest_nodes_states.Keys
    }

    predicate inv_all_honest_nodes_is_a_quorum(dv: DVState)
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

    predicate inv_nodes_in_consensus_instances_are_in_dv(dv: DVState)
    {
        forall ci | ci in dv.consensus_instances_on_beacon_block.Values
            :: && ci.all_nodes == dv.all_nodes
               && ci.honest_nodes_status.Keys == dv.honest_nodes_states.Keys  
               && ci.honest_nodes_status.Keys <= ci.all_nodes
               && ci.honest_nodes_validity_functions.Keys <= ci.honest_nodes_status.Keys
               && |ci.all_nodes - ci.honest_nodes_status.Keys| <= f(|ci.all_nodes|)
    }

    predicate inv_the_same_node_status_in_dv_and_ci(dv: DVState)
    {
        forall s: Slot ::
            && var ci := dv.consensus_instances_on_beacon_block[s];            
            && dv.all_nodes == ci.all_nodes
            && dv.honest_nodes_states.Keys == ci.honest_nodes_status.Keys
    }

    predicate inv_current_proposer_duty_is_a_rcvd_duty_body(dvc: DVCState)
    {
        dvc.current_proposer_duty.isPresent()
        ==> 
        dvc.current_proposer_duty.safe_get() in dvc.all_rcvd_duties
    }

    predicate inv_current_proposer_duty_is_a_rcvd_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_current_proposer_duty_is_a_rcvd_duty_body(dvc)
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

    predicate inv_only_dv_construct_complete_signing_functions(dv: DVState)
    {
        && inv_only_dv_construct_complete_signed_randao_reveal(dv)
        && inv_only_dv_construct_complete_signed_block(dv)                
    }

    predicate inv_latest_served_duty_is_a_rcvd_duty_body(dvc: DVCState)
    {
        dvc.latest_proposer_duty.isPresent()
        ==> 
        dvc.latest_proposer_duty.safe_get() in dvc.all_rcvd_duties
    }

    predicate inv_latest_served_duty_is_a_rcvd_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_latest_served_duty_is_a_rcvd_duty_body(dvc)
    }

    predicate inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(dvc: DVCState)
    {
        !dvc.latest_proposer_duty.isPresent()
        ==> 
        !dvc.current_proposer_duty.isPresent()
    }

    predicate inv_none_latest_proposer_duty_implies_none_current_proposer_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_none_latest_proposer_duty_implies_none_current_proposer_duty_body(dvc)
    }

    predicate inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(dvc: DVCState)
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

    predicate inv_current_proposer_duty_is_either_none_or_latest_proposer_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_current_proposer_duty_is_either_none_or_latest_proposer_duty_body(dvc)
    }

    predicate inv_available_current_proposer_duty_is_latest_proposer_duty_body(dvc: DVCState)
    {
        dvc.current_proposer_duty.isPresent()
        ==> 
        ( && dvc.latest_proposer_duty.isPresent()
          && dvc.current_proposer_duty.safe_get()
                                == dvc.latest_proposer_duty.safe_get()                   
        )
    }

    predicate inv_available_current_proposer_duty_is_latest_proposer_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::            
            && var dvc := dv.honest_nodes_states[hn];
            && inv_available_current_proposer_duty_is_latest_proposer_duty_body(dvc)
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

    predicate inv_unchanged_dv_seq_of_proposer_duties(dv: DVState, dv': DVState)
    {
        dv.sequence_proposer_duties_to_be_served
        == 
        dv'.sequence_proposer_duties_to_be_served
    }

    predicate inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(dvc: DVCState)
    {
        !dvc.latest_proposer_duty.isPresent()
        ==> 
        dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys == {}
    }

    predicate inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_dvc_has_no_active_consensus_instances_if_latest_proposer_duty_is_none_body(dvc)
    }


    predicate inv_available_current_proposer_duty_is_from_dv_seq_of_proposer_duties_body(  
        dvc: DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    {
        dvc.current_proposer_duty.isPresent()
        ==>
        (   && var proposer_duty := dvc.current_proposer_duty.safe_get();
            && exists i: Slot :: 
                    && i < index_next_proposer_duty_to_be_served
                    && var an := sequence_proposer_duties_to_be_served[i];
                    && an.proposer_duty == proposer_duty
                    && an.node == hn
        )
    } 

    predicate inv_available_current_proposer_duty_is_from_dv_seq_of_proposer_duties(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_available_current_proposer_duty_is_from_dv_seq_of_proposer_duties_body(
                    dvc,
                    hn,
                    dv.sequence_proposer_duties_to_be_served,
                    dv.index_next_proposer_duty_to_be_served
                )
    }  

    predicate pred_proposer_duty_is_from_dv_seq_of_proposer_duties_body(  
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

    predicate inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_helper(  
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

    predicate inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn],
                dv.index_next_proposer_duty_to_be_served
            )                    
    }               

    predicate inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties_body(
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

    predicate inv_every_proposer_duty_before_dv_index_next_proposer_duty_to_be_served_was_delivered_body(dvc: DVCState, duty: ProposerDuty)
    {
        duty in dvc.all_rcvd_duties
    }

    predicate inv_every_proposer_duty_before_dv_index_next_proposer_duty_to_be_served_was_delivered(dv: DVState)
    {
        forall k: nat ::
            && 0 <= k < dv.index_next_proposer_duty_to_be_served
            && dv.sequence_proposer_duties_to_be_served[k].node in dv.honest_nodes_states.Keys
            ==> 
            && var duty_and_node: ProposerDutyAndNode := dv.sequence_proposer_duties_to_be_served[k];
            && var duty := duty_and_node.proposer_duty;
            && var hn := duty_and_node.node;
            && var dvc := dv.honest_nodes_states[hn];
            && inv_every_proposer_duty_before_dv_index_next_proposer_duty_to_be_served_was_delivered_body(dvc, duty)
    }   

    predicate inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(dvc: DVCState)
    {
        forall k: Slot | k in dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys ::
            exists rcvd_duty: ProposerDuty :: 
                && rcvd_duty in dvc.all_rcvd_duties
                && rcvd_duty.slot == k
    }

    predicate inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_dvc_joins_only_consensus_instances_for_which_it_has_received_corresponding_proposer_duties_body(dvc)
    }

    predicate inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(dvc: DVCState)
    {
        forall k: Slot | k in dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys 
            ::
            && dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[k].proposer_duty in dvc.all_rcvd_duties                
            && dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[k].proposer_duty.slot == k
    }

    predicate inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_the_consensus_instance_indexed_k_is_for_the_rcvd_duty_for_slot_k_body(dvc)
    }
             
    predicate inv_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(
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
    
    predicate inv_in_transit_messages_are_in_allMessagesSent(
        dv: DVState
    )
    {
        forall m | m in dv.block_share_network.messagesInTransit
            ::
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

    predicate inv_rcvd_block_shares_are_in_all_sent_messages(
        dv: DVState
    )
    {
        forall hn: BLSPubkey | is_an_honest_node(dv, hn) ::
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

    predicate inv_existing_block_slashing_db_for_sent_vp(
        cid: Slot,
        proposer_duty: ProposerDuty,
        randao_reveal: BLSSignature,
        vp: BeaconBlock -> bool        
    )
    {
        exists  block_slashing_db: set<SlashingDBBlock>
                ::
                inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_body(
                    cid, 
                    proposer_duty,                 
                    block_slashing_db, 
                    randao_reveal,
                    vp
                )
    }  

    predicate inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_body(
        dvc: DVCState,
        cid: Slot
    )
    requires cid in dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks
    {
        var bci := dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid];
        inv_existing_block_slashing_db_for_sent_vp(
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



        

    predicate inv_sent_validity_predicate_is_based_on_rcvd_proposer_duty_and_slashing_db_and_randao_reveal_for_dvc_single_dvc(
        dv: DVState,
        n: BLSPubkey,
        cid: Slot
    )
    requires n in dv.honest_nodes_states.Keys 
    requires cid in dv.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys
    {
        && var dvc := dv.honest_nodes_states[n];
        && var bci := dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid];
        && inv_existing_block_slashing_db_for_sent_vp(
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
            && n in dv.honest_nodes_states.Keys
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


    predicate inv_decided_values_of_consensus_instances_are_decided_by_a_quorum(dv: DVState)
    {
        forall cid |
            && cid in dv.consensus_instances_on_beacon_block.Keys
            && dv.consensus_instances_on_beacon_block[cid].decided_value.isPresent()
            ::
            is_a_valid_decided_value(dv.consensus_instances_on_beacon_block[cid])
    }  

    predicate inv_a_decided_value_of_a_consensus_instance_for_slot_k_is_for_slot_k(dv: DVState)
    {
        forall cid |
            && cid in dv.consensus_instances_on_beacon_block.Keys
            && dv.consensus_instances_on_beacon_block[cid].decided_value.isPresent()
            ::
            dv.consensus_instances_on_beacon_block[cid].decided_value.safe_get().slot == cid
    }   

    predicate inv_blocks_of_in_transit_block_shares_are_decided_values(dv: DVState)
    {
        forall hn, block_share |
                && hn in dv.honest_nodes_states.Keys 
                && block_share in dv.block_share_network.allMessagesSent
                && var block_signing_root := compute_block_signing_root(block_share.block);                                      
                && verify_bls_signature(block_signing_root, block_share.signature, hn)
                ::
                inv_blocks_of_in_transit_block_shares_are_decided_values_body(dv, block_share)
    }  

    predicate inv_blocks_of_in_transit_block_shares_are_decided_values_body(dv: DVState, block_share: SignedBeaconBlock)
    {
        && dv.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.isPresent()
        && dv.consensus_instances_on_beacon_block[block_share.block.slot].decided_value.safe_get() == block_share.block
    }  

    predicate inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages_body(
        dv: DVState,
        n: BLSPubkey
    )
    requires n in dv.honest_nodes_states.Keys 
    {
        dv.honest_nodes_states[n].block_shares_to_broadcast.Values <= dv.block_share_network.allMessagesSent
    }

    predicate inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(
        dv: DVState
    )
    {
        forall n |
            n in dv.honest_nodes_states.Keys 
            ::
        inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages_body(dv, n)
    }  

    predicate inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(hn_state: DVCState)    
    {
        forall k: Slot | k in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys ::
            exists duty: ProposerDuty :: 
                    && duty in hn_state.all_rcvd_duties
                    && duty.slot == k
    }

    predicate inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties(dv: DVState)
    {
        forall hn: BLSPubkey | is_an_honest_node(dv, hn) ::
            && var hn_state := dv.honest_nodes_states[hn];            
            && inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(hn_state)       
    }


    predicate inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body_ces(ces: BlockConsensusEngineState)
    {
        forall s: Slot, vp: BeaconBlock -> bool |
                ( && s in ces.block_slashing_db_hist.Keys
                  && vp in ces.block_slashing_db_hist[s].Keys
                )
                :: 
                ( exists db: set<SlashingDBBlock>, duty: ProposerDuty, randao_reveal: BLSSignature ::
                        && duty.slot == s
                        && db in ces.block_slashing_db_hist[s][vp]
                        && vp == (block: BeaconBlock) => ci_decision_is_valid_beacon_block(db, block, duty, randao_reveal)
                )
    }

    predicate inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(hn_state: DVCState)
    {
        forall s: Slot, vp: BeaconBlock -> bool |
                ( && s in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys
                  && vp in hn_state.block_consensus_engine_state.block_slashing_db_hist[s].Keys
                )
                :: 
                ( exists db: set<SlashingDBBlock>, duty: ProposerDuty, randao_reveal: BLSSignature ::
                        && duty.slot == s
                        && db in hn_state.block_consensus_engine_state.block_slashing_db_hist[s][vp]
                        && vp == (block: BeaconBlock) => ci_decision_is_valid_beacon_block(db, block, duty, randao_reveal)
                )
    }

    predicate inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate(dv: DVState)
    {
        forall hn: BLSPubkey | is_an_honest_node(dv, hn) ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(dvc)
    }

    predicate inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(hn_state: DVCState)
    {
        forall k: Slot |
            k in hn_state.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys ::
                && var ci := hn_state.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[k];
                && var vp: BeaconBlock -> bool := ci.validityPredicate;
                && k in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys 
                && vp in hn_state.block_consensus_engine_state.block_slashing_db_hist[k].Keys             
    }

    predicate inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k(dv: DVState)
    {
        forall hn: BLSPubkey | is_an_honest_node(dv, hn) ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_body(dvc)
    }    

    predicate inv_block_slashing_db_hist_is_monotonic_body(dvc: DVCState, dvc': DVCState)
    {        
        dvc.block_consensus_engine_state.block_slashing_db_hist.Keys
        <= 
        dvc'.block_consensus_engine_state.block_slashing_db_hist.Keys
    }

    predicate inv_block_slashing_db_hist_is_monotonic(dv: DVState, event: DV_Block_Proposer_Spec.BlockEvent, dv': DVState)    
    {
        forall hn: BLSPubkey | is_an_honest_node(dv, hn) ::
            && hn in dv'.honest_nodes_states
            && var dvc := dv.honest_nodes_states[hn];
            && var dvc' := dv'.honest_nodes_states[hn];
            && inv_block_slashing_db_hist_is_monotonic_body(dvc, dvc')
    }

    predicate inv_all_blocks_created_is_monotonic(dv: DVState, event: DV_Block_Proposer_Spec.BlockEvent, dv': DVState)    
    {
        dv.all_blocks_created <= dv'.all_blocks_created
    }

    predicate inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body_ces(ces: BlockConsensusEngineState, block_slashing_db: set<SlashingDBBlock>)
    {
        forall s: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> |
                ( && s in ces.block_slashing_db_hist.Keys
                  && vp in ces.block_slashing_db_hist[s].Keys
                  && db in ces.block_slashing_db_hist[s][vp]
                )
                :: 
                db <= block_slashing_db
    }

    predicate inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(hn_state: DVCState)
    {
        forall s: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> |
                ( && s in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys
                  && vp in hn_state.block_consensus_engine_state.block_slashing_db_hist[s].Keys
                  && db in hn_state.block_consensus_engine_state.block_slashing_db_hist[s][vp]
                )
                :: 
                db <= hn_state.block_slashing_db
    }

    predicate inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db(dv: DVState)
    {
        forall hn: BLSPubkey | is_an_honest_node(dv, hn) ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_every_db_in_block_slashing_db_hist_is_a_subset_of_block_slashing_db_body(dvc)
    }


    predicate inv_block_shares_to_broadcast_are_sent_messages_body(
        dv: DVState,
        dvc: DVCState
    )    
    {
        dvc.block_shares_to_broadcast.Values <= dv.block_share_network.allMessagesSent
    }

    predicate inv_block_shares_to_broadcast_are_sent_messages(
        dv: DVState
    )
    {
        forall n | n in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[n];
            && inv_block_shares_to_broadcast_are_sent_messages_body(dv, dvc)
    }

    predicate inv_rcvd_block_shares_are_from_sent_messages_body(
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

    predicate inv_rcvd_block_shares_are_from_sent_messages(
        dv: DVState    
    )
    {
        forall n | n in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[n];
            && inv_rcvd_block_shares_are_from_sent_messages_body(dv, dvc)
    } 

    predicate inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_proposer_duties_body(dvc: DVCState, next_duty: ProposerDuty)
    {
       forall rcvd_duty: ProposerDuty | rcvd_duty in dvc.all_rcvd_duties ::
            rcvd_duty.slot <= next_duty.slot        
    }

    predicate inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_proposer_duties(dv: DVState)
    {
        && var dv_duty_queue := dv.sequence_proposer_duties_to_be_served;
        && var dv_index := dv.index_next_proposer_duty_to_be_served;
        && var next_duty_and_node := dv_duty_queue[dv_index];
        && forall hn: BLSPubkey | 
            && hn in dv.honest_nodes_states.Keys
            && hn == next_duty_and_node.node 
            ::            
            && var dvc := dv.honest_nodes_states[hn];
            && var next_duty := next_duty_and_node.proposer_duty;
            && inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_proposer_duties_body(dvc, next_duty)
    }

    predicate inv_slots_of_active_consensus_instances_are_lower_than_the_slot_of_latest_proposer_duty_body(dvc: DVCState)
    {
        dvc.latest_proposer_duty.isPresent()
        ==> 
        (   forall k: Slot | k in dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys 
            ::
            k < dvc.latest_proposer_duty.safe_get().slot
        )
    }

    predicate inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(dvc: DVCState)
    {
        dvc.latest_proposer_duty.isPresent()
        ==> 
        (   forall k: Slot | k in dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys 
            ::
            k <= dvc.latest_proposer_duty.safe_get().slot
        )
    }

    predicate inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_slots_of_active_consensus_instances_are_not_higher_than_the_slot_of_latest_proposer_duty_body(dvc)
    }

    predicate inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        n_state: DVCState,
        index_next_proposer_duty_to_be_served: nat
    )
    {
        forall slot | slot in n_state.block_consensus_engine_state.block_slashing_db_hist.Keys
            ::
            exists i: Slot :: 
                && i < index_next_proposer_duty_to_be_served
                && var pn := sequence_proposer_duties_to_be_served[i];
                && pn.proposer_duty.slot == slot 
                && pn.node == n
    }          

    predicate inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_exists_a_proposer_duty_in_dv_seq_of_proposer_duties_for_every_slot_in_block_slashing_db_hist_body(
                dv.sequence_proposer_duties_to_be_served, 
                hn,
                dv.honest_nodes_states[hn],
                dv.index_next_proposer_duty_to_be_served
            )                    
    }       

    function get_upperlimit_active_instances(
        n_state: DVCState
    ): nat 
    {
        if n_state.latest_proposer_duty.isPresent() then
            n_state.latest_proposer_duty.safe_get().slot + 1
        else
            0
    }                
           
    predicate inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(
        dvc: DVCState       
    )
    {
        forall slot: Slot | slot in dvc.block_consensus_engine_state.block_slashing_db_hist.Keys
            ::
            slot < get_upperlimit_active_instances(dvc)
    }     

    predicate inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty(
        dv: DVState        
    )
    {
        forall hn: BLSPubkey | is_an_honest_node(dv, hn) ::
                inv_slots_of_consensus_instances_are_up_to_the_slot_of_latest_proposer_duty_body(dv.honest_nodes_states[hn])        
    }     

    // TODO: Investigate
    predicate inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(
        dv: DVState, 
        n: BLSPubkey,
        n_state: DVCState
    )
    {
        forall slot |
            && slot in n_state.future_consensus_instances_on_blocks_already_decided.Keys    
            ::
            && dv.consensus_instances_on_beacon_block[slot].decided_value.isPresent()
            && n_state.future_consensus_instances_on_blocks_already_decided[slot] == dv.consensus_instances_on_beacon_block[slot].decided_value.safe_get()
    }  

    predicate inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_future_decided_blocks_known_by_dvc_are_decisions_of_quorums_body(
                dv, 
                hn,
                dv.honest_nodes_states[hn]
            )                    
    }       

    predicate inv_slots_in_future_decided_beacon_blocks_are_correct_body(
        n_state: DVCState
    )
    {
        forall slot |
            && slot in n_state.future_consensus_instances_on_blocks_already_decided.Keys
            ::
            n_state.future_consensus_instances_on_blocks_already_decided[slot].slot == slot
    }  

    predicate inv_slots_in_future_decided_beacon_blocks_are_correct(dv: DVState)    
    {
        forall hn |
            && hn in dv.honest_nodes_states.Keys          
            ::
            inv_slots_in_future_decided_beacon_blocks_are_correct_body(
                dv.honest_nodes_states[hn]
            )                    
    }              

    predicate inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
        dvc: DVCState,
        hn: BLSPubkey,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    {
       forall proposer_duty |
            proposer_duty in dvc.all_rcvd_duties
            ::
            inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_helper(                
                proposer_duty, 
                hn, 
                sequence_proposer_duties_to_be_served,
                index_next_proposer_duty_to_be_served)
    }

    predicate inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body_helper(        
        proposer_duty: ProposerDuty,
        hn: BLSPubkey, 
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,    
        index_next_proposer_duty_to_be_served: nat
    )
    {
            exists i ::
                && 0 <= i
                && i < index_next_proposer_duty_to_be_served 
                && var duty_and_node := sequence_proposer_duties_to_be_served[i];
                && duty_and_node.node == hn
                && duty_and_node.proposer_duty == proposer_duty
    }

    predicate inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty(dv: DVState)
    {
        forall hn: BLSPubkey | 
            is_an_honest_node(dv, hn) 
            ::
            && var hn_state := dv.honest_nodes_states[hn];
            && inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(                    
                    hn_state, 
                    hn, 
                    dv.sequence_proposer_duties_to_be_served,
                    dv.index_next_proposer_duty_to_be_served)
    }  

    predicate inv_sent_validity_predicate_only_for_slots_stored_in_block_slashing_db_hist(dv: DVState)
    {
        forall hn: BLSPubkey, s: Slot | is_an_honest_node(dv, hn) ::
            && var hn_state := dv.honest_nodes_states[hn];
            && ( hn in dv.consensus_instances_on_beacon_block[s].honest_nodes_validity_functions.Keys
                 ==> 
                 s in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys)
    }

    predicate inv_all_validity_predicates_are_stored_in_block_slashing_db_hist_body(
        dv: DVState, 
        hn: BLSPubkey,
        hn_state: DVCState,
        s: Slot,
        vp: BeaconBlock -> bool
    )
    requires && hn in dv.honest_nodes_states.Keys
             && hn_state == dv.honest_nodes_states[hn]
             && hn in dv.consensus_instances_on_beacon_block[s].honest_nodes_validity_functions.Keys
             && s in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys
             && vp in dv.consensus_instances_on_beacon_block[s].honest_nodes_validity_functions[hn]
    {        
        vp in hn_state.block_consensus_engine_state.block_slashing_db_hist[s].Keys
    }

    predicate inv_all_validity_predicates_are_stored_in_block_slashing_db_hist_helper(
        dv: DVState, 
        hn: BLSPubkey
    )
    requires hn in dv.honest_nodes_states.Keys
    {
        && var hn_state := dv.honest_nodes_states[hn];
        && forall cid: Slot, vp : BeaconBlock -> bool |
                && hn in dv.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions.Keys
                && cid in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys
                && vp in dv.consensus_instances_on_beacon_block[cid].honest_nodes_validity_functions[hn]
                :: 
                inv_all_validity_predicates_are_stored_in_block_slashing_db_hist_body(
                    dv,
                    hn,
                    dv.honest_nodes_states[hn],
                    cid,
                    vp
                )
    }       
    
    predicate inv_all_validity_predicates_are_stored_in_block_slashing_db_hist(dv: DVState)
    {
        forall hn: BLSPubkey |
            hn in dv.honest_nodes_states.Keys
            ::
            inv_all_validity_predicates_are_stored_in_block_slashing_db_hist_helper(
                dv,
                hn
            )
    }              

    predicate inv_unique_rcvd_proposer_duty_per_slot_body_premises(
        dvc: DVCState,
        d1: ProposerDuty, 
        d2: ProposerDuty 
    )
    {
        (   && d1 in dvc.all_rcvd_duties
            && d2 in dvc.all_rcvd_duties
            && d1.slot == d2.slot
        )
    }

    predicate inv_unique_rcvd_proposer_duty_per_slot_body_helper(
        dvc: DVCState,
        d1: ProposerDuty, 
        d2: ProposerDuty 
    )
    {
        (   && d1 in dvc.all_rcvd_duties
            && d2 in dvc.all_rcvd_duties
            && d1.slot == d2.slot
        )
        ==>
        d1 == d2
    }

    predicate inv_unique_rcvd_proposer_duty_per_slot_body(dvc: DVCState)
    {
        forall d1: ProposerDuty, d2: ProposerDuty ::
            ( && d1 in dvc.all_rcvd_duties
              && d2 in dvc.all_rcvd_duties
              && d1.slot == d2.slot
            )
            ==>
            d1 == d2
    }

    predicate inv_unique_rcvd_proposer_duty_per_slot(dv: DVState)
    {
        forall hn: BLSPubkey | 
            is_an_honest_node(dv, hn) 
            ::
            inv_unique_rcvd_proposer_duty_per_slot_body(dv.honest_nodes_states[hn])
    }



    predicate inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_proposer_duty_and_randao_reveal_body(
        dv: DVState, 
        hn: BLSPubkey, 
        s: Slot, 
        db: set<SlashingDBBlock>, 
        duty: ProposerDuty, 
        vp: BeaconBlock -> bool,
        randao_reveal: BLSSignature
    )
    requires && is_an_honest_node(dv, hn)
             && var hn_state := dv.honest_nodes_states[hn];
             && s in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys
             && vp in hn_state.block_consensus_engine_state.block_slashing_db_hist[s].Keys
    {
        && var hn_state := dv.honest_nodes_states[hn];
        && duty.slot == s
        && db in hn_state.block_consensus_engine_state.block_slashing_db_hist[s][vp]
        && vp == (bb: BeaconBlock) => ci_decision_is_valid_beacon_block(db, bb, duty, randao_reveal)
    }

    predicate inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_proposer_duty_and_randao_reveal(dv: DVState)
    {
        forall hn: BLSPubkey, s: Slot, vp: BeaconBlock -> bool | 
            && is_an_honest_node(dv, hn)
            && var hn_state := dv.honest_nodes_states[hn];
            && s in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys
            && vp in hn_state.block_consensus_engine_state.block_slashing_db_hist[s].Keys
            ::
            exists duty, db, randao_reveal ::
                && var hn_state := dv.honest_nodes_states[hn];
                && inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_proposer_duty_and_randao_reveal_body(dv, hn, s, db, duty, vp, randao_reveal)
    }
    
    predicate inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block_body<D(!new, 0)>(ci: BlockConsensusInstance) 
    {
        ci.decided_value.isPresent()
        ==> 
        is_a_valid_decided_value(ci)
    }
    
    predicate inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block(dv: DVState)
    {
        forall s: Slot ::
            && var ci := dv.consensus_instances_on_beacon_block[s];
            && inv_exists_an_honest_dvc_as_a_witness_for_every_decided_beacon_block_body(ci)            
    }

    predicate inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty_body(dvc: DVCState, next_duty: ProposerDuty)
    {
        dvc.latest_proposer_duty.isPresent()
        ==> 
        dvc.latest_proposer_duty.safe_get().slot < next_duty.slot        
    }

    predicate inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty(dv: DVState)
    {
        && var dv_duty_queue := dv.sequence_proposer_duties_to_be_served;
        && var dv_index := dv.index_next_proposer_duty_to_be_served;
        && var next_duty_and_node := dv_duty_queue[dv_index];
        && forall hn: BLSPubkey | 
            && hn in dv.honest_nodes_states.Keys
            && hn == next_duty_and_node.node 
            ::            
            && var dvc := dv.honest_nodes_states[hn];
            && var next_duty := next_duty_and_node.proposer_duty;
            && inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty_body(dvc, next_duty)
    }

    predicate inv_active_consensus_instances_implied_the_delivery_of_proposer_duties_body(hn_state: DVCState, s: Slot)
    requires s in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys
    {
        exists duty: ProposerDuty :: 
                    && duty in hn_state.all_rcvd_duties
                    && duty.slot == s
    }

    predicate inv_active_consensus_instances_implied_the_delivery_of_proposer_duties(dv: DVState)
    {
        forall hn: BLSPubkey, s: Slot ::
            ( && is_an_honest_node(dv, hn) 
              && var hn_state := dv.honest_nodes_states[hn];
              && s in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys
            )
            ==>
            inv_active_consensus_instances_implied_the_delivery_of_proposer_duties_body(dv.honest_nodes_states[hn], s)                
    }

    predicate inv_block_slashing_db_is_monotonic_body(dvc: DVCState, dvc': DVCState)
    {
        dvc.block_slashing_db <= dvc'.block_slashing_db
    }

    predicate inv_block_slashing_db_is_monotonic(dv: DVState, event: DV_Block_Proposer_Spec.BlockEvent, dv': DVState)    
    {
        forall hn: BLSPubkey | is_an_honest_node(dv, hn) ::
            && hn in dv'.honest_nodes_states.Keys
            && var dvc := dv.honest_nodes_states[hn];
            && var dvc' := dv'.honest_nodes_states[hn];
            && inv_block_slashing_db_is_monotonic_body(dvc, dvc')
    }

    
    predicate inv_unchanged_rs_body(dvc: DVCState, dvc': DVCState)
    {
        dvc.rs.pubkey == dvc'.rs.pubkey
    }

    predicate inv_constraints_on_active_consensus_instances_on_beacon_blocks_are_ensured_with_block_slashing_db_hist(dv: DVState)    
    {
        forall hn, cid |
            && hn in dv.honest_nodes_states.Keys        
            ::
            inv_constraints_on_active_consensus_instances_on_beacon_blocks_are_ensured_with_block_slashing_db_hist_body(dv.honest_nodes_states[hn], cid)
             
    }       

    predicate inv_constraints_on_active_consensus_instances_on_beacon_blocks_are_ensured_with_block_slashing_db_hist_body
    (
        n_state: DVCState,
        cid: Slot
    )
    {
        && cid in n_state.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys 
        ==>
        (
            && cid in n_state.block_consensus_engine_state.block_slashing_db_hist.Keys  
            && n_state.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid].validityPredicate in n_state.block_consensus_engine_state.block_slashing_db_hist[cid].Keys
        )
    }  
   
    predicate inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(dvc: DVCState)
    {
        dvc.block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys 
        <= 
        dvc.block_consensus_engine_state.block_slashing_db_hist.Keys
    } 

    predicate inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist(dv: DVState)
    {
        forall hn | hn in dv.honest_nodes_states.Keys ::
            && var dvc := dv.honest_nodes_states[hn];
            && inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist_body(dvc)
    } 
    
    predicate inv_slots_for_sent_validity_predicates_are_stored_in_block_slashing_db_hist_body(
        dv: DVState, 
        hn: BLSPubkey,
        hn_state: DVCState,
        s: Slot
    )
    {
        hn in dv.consensus_instances_on_beacon_block[s].honest_nodes_validity_functions.Keys
        ==> 
        s in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys
    }

    predicate inv_slots_for_sent_validity_predicates_are_stored_in_block_slashing_db_hist(dv: DVState)
    {
        forall hn: BLSPubkey, s: Slot |
            hn in dv.honest_nodes_states.Keys
            :: 
            inv_slots_for_sent_validity_predicates_are_stored_in_block_slashing_db_hist_body(dv, hn, dv.honest_nodes_states[hn], s)        
    } 


    predicate inv_consensus_instance_isConditionForSafetyTrue(dv: DVState)
    {
        forall slot: Slot | slot in dv.consensus_instances_on_beacon_block.Keys  ::
                    isConditionForSafetyTrue(dv.consensus_instances_on_beacon_block[slot])                    
    }

    predicate pred_last_proposer_duty_is_delivering_to_given_honest_node(
        proposer_duty: ProposerDuty,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        n: BLSPubkey,
        index_next_proposer_duty_to_be_served: nat
    )
    {
        && 0 < index_next_proposer_duty_to_be_served 
        && var i := index_next_proposer_duty_to_be_served - 1;
        && var pn := sequence_proposer_duties_to_be_served[i];
        && pn.proposer_duty == proposer_duty
        && pn.node == n
    }

    predicate inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(dvc: DVCState)
    {
        !dvc.latest_proposer_duty.isPresent()
        <==> 
        dvc.all_rcvd_duties == {}
    }

    predicate inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            inv_none_latest_proposer_duty_and_empty_set_of_rcvd_proposer_duties_body(dv.honest_nodes_states[hn])
    }

    predicate inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(dvc: DVCState)
    {
        dvc.latest_proposer_duty.isPresent()
        ==>
        ( forall proposer_duty | proposer_duty in dvc.all_rcvd_duties ::
            proposer_duty.slot <= dvc.latest_proposer_duty.safe_get().slot
        )
    }

    predicate inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty(dv: DVState)
    {
        forall hn: BLSPubkey | hn in dv.honest_nodes_states.Keys ::
            &&  var dvc := dv.honest_nodes_states[hn];
            &&  inv_no_rcvd_proposer_duty_is_higher_than_latest_proposer_duty_body(dvc)
    }

    predicate inv_block_of_all_created_blocks_is_set_of_decided_values(dv: DVState)
    {
        forall complete_block | complete_block in dv.all_blocks_created ::
                && var consa := dv.consensus_instances_on_beacon_block[complete_block.block.slot];
                && consa.decided_value.isPresent() 
                && complete_block.block == consa.decided_value.safe_get() 
    }

    predicate inv_all_created_signed_beacon_blocks_are_valid(dv: DVState)
    {
        forall b | b in dv.all_blocks_created ::
                is_valid_signed_beacon_block(b, dv.dv_pubkey)
    }

    predicate inv_submitted_outputs_blocks_are_valid(
        outputs: Outputs,
        dv_pubkey: BLSPubkey)
    {
        forall submitted_block | submitted_block in outputs.submitted_blocks ::
            is_valid_signed_beacon_block(submitted_block, dv_pubkey)
    }

    predicate pred_is_the_owner_of_a_block_share(
        rs_pubkey: BLSPubkey,
        block_share: SignedBeaconBlock
    )
    {
        && var decided_beacon_block := block_share.block;
        && var block_signing_root := compute_block_signing_root(decided_beacon_block);
        && verify_bls_signature(block_signing_root, block_share.signature, rs_pubkey)
    }

    predicate inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_body(
        dvc: DVCState, 
        block_share: SignedBeaconBlock
    )
    {
        && var beacon_block: BeaconBlock := block_share.block;
        && var slashing_db_block := construct_SlashingDBBlock_from_beacon_block(beacon_block);
        && slashing_db_block in dvc.block_slashing_db  
        && var rs_pubkey: BLSPubkey := dvc.rs.pubkey;    
        && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
    }   

                         
    predicate inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db(
        outputs: Outputs,
        dvc: DVCState)
    {
        forall block_share: SignedBeaconBlock | 
            block_share in getMessagesFromMessagesWithRecipient(outputs.sent_block_shares) 
            ::
            inv_outputs_sent_block_shares_are_tracked_in_block_slashing_db_body(dvc, block_share)
    } 

    predicate inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(
        dvc: DVCState
    )
    {
        forall slot: Slot | 
            slot in dvc.block_shares_to_broadcast.Keys
            ::
            && var block_share: SignedBeaconBlock := dvc.block_shares_to_broadcast[slot];
            && var beacon_block: BeaconBlock := block_share.block;
            && var slashing_db_block := construct_SlashingDBBlock_from_beacon_block(beacon_block);
            && slashing_db_block in dvc.block_slashing_db  
            && var rs_pubkey: BLSPubkey := dvc.rs.pubkey;    
            && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
    }   

    predicate inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db(
        dv: DVState)
    {
        forall hn: BLSPubkey | 
            is_an_honest_node(dv, hn)
            ::
            inv_block_shares_to_broadcast_are_tracked_in_block_slashing_db_body(dv.honest_nodes_states[hn])
    } 

    predicate inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(
        dvc: DVCState,
        block_share: SignedBeaconBlock
    )
    {
        && var beacon_block := block_share.block;
        && var slashing_db_block := construct_SlashingDBBlock_from_beacon_block(beacon_block);
        && slashing_db_block in dvc.block_slashing_db     
    }

    predicate inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks(
        dv: DVState
    )
    {
        forall hn: BLSPubkey, block_share: SignedBeaconBlock | 
            && is_an_honest_node(dv, hn)
            && block_share in dv.block_share_network.allMessagesSent 
            && var dvc: DVCState := dv.honest_nodes_states[hn];
            && var rs_pubkey: BLSPubkey := dvc.rs.pubkey;
            && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
            ::
            && var dvc: DVCState := dv.honest_nodes_states[hn];
            && inv_sent_block_shares_have_corresponding_stored_slashing_db_blocks_body(dvc, block_share)            
    }

    predicate inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_body_signers_helper(
        block_shares: set<SignedBeaconBlock>,
        dvc: DVCState
    )
    {
        exists block_share: SignedBeaconBlock ::
            && block_share in block_shares
            && var rs_pubkey := dvc.rs.pubkey;
            && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
    }

    predicate inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_body_signers(
        dv: DVState,
        block_shares: set<SignedBeaconBlock>,
        dvc_signer_pubkeys: set<BLSPubkey>
    )
    {
        forall key: BLSPubkey | key in dvc_signer_pubkeys ::
            key in dv.honest_nodes_states.Keys
            ==>
            inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_body_signers_helper(
                    block_shares,
                    dv.honest_nodes_states[key]
                )        
    }

    predicate inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_body_helper(
        dv: DVState, 
        complete_block: SignedBeaconBlock,
        block_shares: set<SignedBeaconBlock>,
        dvc_signer_pubkeys: set<BLSPubkey>
    )
    {
        && block_shares <= dv.block_share_network.allMessagesSent
        && dv.construct_complete_signed_block(block_shares).isPresent()
        && complete_block == dv.construct_complete_signed_block(block_shares).safe_get()
        && signed_beacon_blocks_for_the_same_beacon_block(block_shares, complete_block.block)
        && dvc_signer_pubkeys <= dv.all_nodes
        && inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_body_signers(dv, block_shares, dvc_signer_pubkeys)
        && |dvc_signer_pubkeys| >= quorum(|dv.all_nodes|)
    }

    predicate inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_body(
        dv: DVState, 
        complete_block: SignedBeaconBlock        
    )
    {
        exists block_shares, dvc_signer_pubkeys ::             
                && block_shares <= dv.block_share_network.allMessagesSent
                && dv.construct_complete_signed_block(block_shares).isPresent()
                && complete_block == dv.construct_complete_signed_block(block_shares).safe_get()
                && signed_beacon_blocks_for_the_same_beacon_block(block_shares, complete_block.block)
                && dvc_signer_pubkeys <= dv.all_nodes
                && inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_body_signers(dv, block_shares, dvc_signer_pubkeys)
                && |dvc_signer_pubkeys| >= quorum(|dv.all_nodes|)
    }

    predicate inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum(dv: DVState)
    {
        forall complete_block: SignedBeaconBlock | complete_block in dv.all_blocks_created ::
                inv_a_complete_signed_block_is_created_based_on_shares_from_a_quorum_body(dv, complete_block)
    }

    predicate inv_a_complete_block_is_created_based_on_shares_from_a_quorum_of_rs_signers_body(
        block_shares: set<SignedBeaconBlock>,
        rs_signer_pubkey: BLSPubkey
    )
    {
        exists block_share: SignedBeaconBlock ::
            && block_share in block_shares
            && pred_is_the_owner_of_a_block_share(rs_signer_pubkey, block_share)
    }

    predicate inv_a_complete_block_is_created_based_on_shares_from_a_quorum_of_rs_signers(
        block_shares: set<SignedBeaconBlock>,
        rs_signer_pubkeys: set<BLSPubkey>
    )
    {
        forall key: BLSPubkey | key in rs_signer_pubkeys ::
                inv_a_complete_block_is_created_based_on_shares_from_a_quorum_of_rs_signers_body(
                    block_shares,
                    key
                )        
    }

    predicate inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum_body(
        dvc: DVCState, 
        complete_block: SignedBeaconBlock
    )
    {
        && complete_block.block.slot in dvc.rcvd_block_shares.Keys
        && exists block_shares, rs_signer_pubkeys, k ::          
                && k in dvc.rcvd_block_shares[complete_block.block.slot].Keys
                && block_shares <= dvc.rcvd_block_shares[complete_block.block.slot][k]
                && dvc.construct_complete_signed_block(block_shares).isPresent()
                && complete_block == dvc.construct_complete_signed_block(block_shares).safe_get()
                && signed_beacon_blocks_for_the_same_beacon_block(block_shares, complete_block.block)
                && inv_a_complete_block_is_created_based_on_shares_from_a_quorum_of_rs_signers(block_shares, rs_signer_pubkeys)
                && |rs_signer_pubkeys| >= quorum(|dvc.peers|)
                && rs_signer_pubkeys <= dvc.peers
    }   

    predicate inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum(
        outputs: Outputs,
        dvc: DVCState)
    {
        forall submitted_block | submitted_block in outputs.submitted_blocks ::
            inv_outputs_blocks_submited_are_created_based_on_shares_from_a_quorum_body(dvc, submitted_block)
    } 

    predicate inv_blocks_of_submitted_signed_blocks_are_decided_values_body(
        dv: DVState,
        complete_block: SignedBeaconBlock
    )
    {
        && complete_block in dv.all_blocks_created
        && var beacon_block: BeaconBlock := complete_block.block;
        && var slot := beacon_block.slot;
        && dv.consensus_instances_on_beacon_block[slot].decided_value.isPresent()
        && dv.consensus_instances_on_beacon_block[slot].decided_value.safe_get() == beacon_block
    }

    predicate inv_blocks_of_submitted_signed_blocks_are_decided_values(
        dv: DVState
    )
    {
        forall complete_block: SignedBeaconBlock | 
            complete_block in dv.all_blocks_created
            ::
            && var beacon_block: BeaconBlock := complete_block.block;
            && var slot := beacon_block.slot;
            && dv.consensus_instances_on_beacon_block[slot].decided_value.isPresent()
            && dv.consensus_instances_on_beacon_block[slot].decided_value.safe_get() == beacon_block
    }

    predicate inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_body(
        dv: DVState,
        hn: BLSPubkey,
        slot: Slot, 
        vp: BeaconBlock -> bool, 
        db: set<SlashingDBBlock>
    )
    {
        && is_an_honest_node(dv, hn) 
        && var dvc := dv.honest_nodes_states[hn];
        && var rs_pubkey := dvc.rs.pubkey;
        && ( forall block_share: SignedBeaconBlock | 
                && block_share in dv.block_share_network.allMessagesSent
                && is_an_honest_node(dv, hn)
                && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
                && block_share.block.slot < slot
                ::
                && var beacon_block := block_share.block;
                && var slashing_db_block := construct_SlashingDBBlock_from_beacon_block(beacon_block);
                && slashing_db_block in db
            )
    }

    predicate inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_helper(
        dv: DVState,
        hn: BLSPubkey
    )
    {
        && is_an_honest_node(dv, hn) 
        && var dvc := dv.honest_nodes_states[hn];
        && forall slot: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> | 
                && slot in dvc.block_consensus_engine_state.block_slashing_db_hist
                && vp in dvc.block_consensus_engine_state.block_slashing_db_hist[slot].Keys
                && db in dvc.block_consensus_engine_state.block_slashing_db_hist[slot][vp]
                :: 
                inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_body(
                    dv,
                    hn,
                    slot,
                    vp,
                    db)
    }

    predicate inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots(dv: DVState)
    {
        forall hn: BLSPubkey | is_an_honest_node(dv, hn) 
            ::
            inv_db_of_vp_contains_all_beacon_block_of_sent_block_shares_with_lower_slots_helper(dv, hn)
    }

    predicate inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body_conclusion(
        allMessagesSent: set<SignedBeaconBlock>,
        rs_pubkey: BLSPubkey,
        slot: Slot, 
        vp: BeaconBlock -> bool, 
        db: set<SlashingDBBlock>,
        block_share: SignedBeaconBlock
    )
    {
        && var beacon_block := block_share.block;
        && var slashing_db_block := construct_SlashingDBBlock_from_beacon_block(beacon_block);        
        && slashing_db_block in db
    }

    predicate inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(
        allMessagesSent: set<SignedBeaconBlock>,
        rs_pubkey: BLSPubkey,
        slot: Slot, 
        vp: BeaconBlock -> bool, 
        db: set<SlashingDBBlock>
    )
    {
        forall block_share: SignedBeaconBlock | 
            && block_share in allMessagesSent
            && pred_is_the_owner_of_a_block_share(rs_pubkey, block_share)
            && block_share.block.slot < slot
            ::
            inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body_conclusion(
                allMessagesSent,
                rs_pubkey,
                slot,
                vp,
                db,
                block_share
            )
    }

    predicate inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc(
        allMessagesSent: set<SignedBeaconBlock>,
        dvc: DVCState        
    )
    {
        forall slot: Slot, vp: BeaconBlock -> bool, db: set<SlashingDBBlock> | 
            && slot in dvc.block_consensus_engine_state.block_slashing_db_hist
            && vp in dvc.block_consensus_engine_state.block_slashing_db_hist[slot].Keys
            && db in dvc.block_consensus_engine_state.block_slashing_db_hist[slot][vp]
            :: 
            inv_db_of_vp_from_a_sent_block_share_contains_all_beacon_blocks_of_sent_block_shares_with_lower_slots_dvc_body(
                allMessagesSent,
                dvc.rs.pubkey,
                slot,
                vp,
                db
            )
    }

    predicate inv_unchanged_dvc_rs_pubkey(dv: DVState)
    {
        forall hn: BLSPubkey | is_an_honest_node(dv, hn) ::
            && var dvc: DVCState := dv.honest_nodes_states[hn];
            && dvc.rs.pubkey == hn
    }

    predicate inv_honest_nodes_are_not_owners_of_block_shares_from_adversary_body(
        dv: DVState, 
        block_share: SignedBeaconBlock
    )
    {
        forall hn: BLSPubkey | is_an_honest_node(dv, hn) :: 
            !pred_is_the_owner_of_a_block_share(hn, block_share)
    }

    predicate inv_honest_nodes_are_not_owners_of_block_shares_from_adversary(dv: DVState)
    {
        forall byz_node: BLSPubkey, block_share: SignedBeaconBlock | 
            && byz_node in dv.adversary.nodes 
            && block_share in dv.block_share_network.allMessagesSent
            && pred_is_the_owner_of_a_block_share(byz_node, block_share)
            ::
            inv_honest_nodes_are_not_owners_of_block_shares_from_adversary_body(dv, block_share)
    }

    predicate inv_stored_SlashingDBBlocks_have_available_signing_root_body(dvc: DVCState)
    {
        forall slashing_db_block: SlashingDBBlock | 
                slashing_db_block in dvc.block_slashing_db
                ::
                slashing_db_block.signing_root.isPresent()
    }

    predicate inv_stored_SlashingDBBlocks_have_available_signing_root(dv: DVState)
    {
        forall hn | is_an_honest_node(dv, hn) ::
            inv_stored_SlashingDBBlocks_have_available_signing_root_body(dv.honest_nodes_states[hn])
    }

    predicate inv_at_most_one_submitted_signed_beacon_block_with_an_available_signing_root_for_every_slot(dv: DVState)
    {
        forall sbb1, sbb2: SignedBeaconBlock |
            && sbb1 in dv.all_blocks_created
            && sbb2 in dv.all_blocks_created
            && sbb1.block.slot == sbb2.block.slot
            ::
            && var bb1 := sbb1.block;
            && var bb2 := sbb2.block;
            && var sdbb1 := construct_SlashingDBBlock_from_beacon_block(bb1);
            && var sdbb2 := construct_SlashingDBBlock_from_beacon_block(bb2);
            && sdbb1.signing_root.isPresent()
            && sdbb2.signing_root.isPresent()
            && sdbb1.signing_root.safe_get() == sdbb2.signing_root.safe_get()
    }

    predicate inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(dvc: DVCState)
    {   
        dvc.latest_proposer_duty.isPresent()
        ==>
        ( && var slot := dvc.latest_proposer_duty.safe_get().slot;
          && forall slashing_db_block: SlashingDBBlock | slashing_db_block in dvc.block_slashing_db
                ::
                slashing_db_block.slot <= slot
        )
    }

    predicate inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty(dv: DVState)
    {
        forall hn | is_an_honest_node(dv, hn) ::
            inv_slots_in_slashing_db_is_not_higher_than_the_slot_of_latest_proposer_duty_body(dv.honest_nodes_states[hn])
    }

    predicate inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(dvc: DVCState)
    {
        !dvc.latest_proposer_duty.isPresent()
        ==>
        dvc.block_slashing_db == {}
    }

    predicate inv_none_latest_proposer_duty_implies_emply_block_slashing_db(dv: DVState)
    {
        forall hn | is_an_honest_node(dv, hn) ::
            inv_none_latest_proposer_duty_implies_emply_block_slashing_db_body(dv.honest_nodes_states[hn])
    }

    predicate inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(dvc: DVCState)
    {
        !dvc.latest_slashing_db_block.isPresent()
        ==>
        dvc.block_slashing_db == {}
    }

    predicate inv_none_latest_slashing_db_block_implies_emply_block_slashing_db(dv: DVState)
    {
        forall hn | is_an_honest_node(dv, hn) ::
            inv_none_latest_slashing_db_block_implies_emply_block_slashing_db_body(dv.honest_nodes_states[hn])
    }

    predicate inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(dvc: DVCState)
    {   
        dvc.latest_slashing_db_block.isPresent()
        ==>
        ( && var slot := dvc.latest_slashing_db_block.safe_get().slot;
          && forall slashing_db_block: SlashingDBBlock | slashing_db_block in dvc.block_slashing_db
                ::
                slashing_db_block.slot <= slot
        )
    }

    predicate inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block(dv: DVState)
    {
        forall hn | is_an_honest_node(dv, hn) ::
            inv_slots_in_slashing_db_are_not_higher_than_the_slot_of_latest_slashing_db_block_body(dv.honest_nodes_states[hn])
    }
}