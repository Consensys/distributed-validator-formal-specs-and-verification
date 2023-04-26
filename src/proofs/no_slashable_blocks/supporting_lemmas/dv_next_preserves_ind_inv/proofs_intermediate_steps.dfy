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

include "../../../common/helper_sets_lemmas.dfy"

include "../../../common/helper_pred_fcn.dfy"
module Proofs_Intermediate_Steps
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
    
    lemma lem_inv_the_same_node_status_in_dv_and_ci_ind_inv(dv: DVState)
    requires inv_nodes_in_consensus_instances_are_in_dv(dv)
    ensures inv_the_same_node_status_in_dv_and_ci(dv)
    { }
        
    lemma lem_inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty_ind_inv(
        dv: DVState
    )         
    requires inv_current_proposer_duty_is_a_rcvd_duty(dv)    
    requires inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_proposer_duties(dv)
    requires inv_available_latest_proposer_duty_is_from_dv_seq_of_proposer_duties(dv) 
    requires inv_seq_of_proposer_duties_is_ordered(dv)  
    ensures inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty(dv)
    {   
        var queue := dv.sequence_proposer_duties_to_be_served;
        var index := dv.index_next_proposer_duty_to_be_served;        
        var next_duty := queue[index].proposer_duty;
        var hn := queue[index].node;


        if hn in dv.honest_nodes_states.Keys 
        {
            var dvc := dv.honest_nodes_states[hn];
            if dvc.latest_proposer_duty.isPresent()
            {
                var duty := dvc.latest_proposer_duty.safe_get();
                var i: Slot :|  && i < index
                                && var pn := queue[i];
                                && pn.proposer_duty == duty
                                && pn.node == hn
                                ;

                assert queue[i].proposer_duty.slot < queue[index].proposer_duty.slot;
                assert inv_proposer_duty_in_next_delivery_is_higher_than_latest_served_proposer_duty_body(dvc, next_duty);
            }
        }
    } 
      
    lemma lem_inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_proposer_duties_ind_inv(
        dv: DVState
    )    
    requires inv_seq_of_proposer_duties_is_ordered(dv)
    requires inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty(dv)
    ensures inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_proposer_duties(dv)    
    {   
        var queue := dv.sequence_proposer_duties_to_be_served;
        var index := dv.index_next_proposer_duty_to_be_served;        
        var next_duty := queue[index].proposer_duty;
        var hn := queue[index].node;

        if hn in dv.honest_nodes_states.Keys 
        {
            var dvc := dv.honest_nodes_states[hn];

            forall rcvd_duty: ProposerDuty | rcvd_duty in dvc.all_rcvd_duties
            ensures rcvd_duty.slot <= next_duty.slot
            {
                assert  inv_rcvd_proposer_duty_is_from_dv_seq_for_rcvd_proposer_duty_body(
                            dvc, 
                            hn, 
                            dv.sequence_proposer_duties_to_be_served,
                            dv.index_next_proposer_duty_to_be_served
                        );

                var k: nat :| && 0 <= k < dv.index_next_proposer_duty_to_be_served
                              && dv.sequence_proposer_duties_to_be_served[k].node == hn
                              && dv.sequence_proposer_duties_to_be_served[k].proposer_duty == rcvd_duty;

                assert dv.sequence_proposer_duties_to_be_served[k].proposer_duty.slot <= next_duty.slot;

                assert rcvd_duty.slot <= next_duty.slot;
            }

            assert inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_proposer_duties_body(dvc, next_duty);
        }        
    }

    lemma lem_inv_active_consensus_instances_implied_the_delivery_of_proposer_duties_ind_inv(
        dv: DVState
    )    
    requires inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties(dv)
    ensures inv_active_consensus_instances_implied_the_delivery_of_proposer_duties(dv)    
    {  
        forall hn: BLSPubkey, s: Slot 
        ensures ( ( && is_an_honest_node(dv, hn) 
                    && s in dv.honest_nodes_states[hn].block_consensus_engine_state.block_slashing_db_hist.Keys
                  )
                  ==> inv_active_consensus_instances_implied_the_delivery_of_proposer_duties_body(dv.honest_nodes_states[hn], s)
                )
        {
            if && is_an_honest_node(dv, hn) 
               && s in dv.honest_nodes_states[hn].block_consensus_engine_state.block_slashing_db_hist.Keys
            {
                var hn_state := dv.honest_nodes_states[hn];
                assert inv_block_slashing_db_hist_keeps_track_of_only_rcvd_proposer_duties_body(hn_state);
                assert inv_active_consensus_instances_implied_the_delivery_of_proposer_duties_body(hn_state, s);
            }
            else
            {}
        }
    } 

    lemma lem_inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_proposer_duty_and_randao_reveal_ind_inv(
        dv: DVState
    )    
    requires inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate(dv)
    ensures inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_proposer_duty_and_randao_reveal(dv)    
    { 
        forall hn: BLSPubkey, s: Slot, vp: BeaconBlock -> bool | 
            && is_an_honest_node(dv, hn)
            && var hn_state := dv.honest_nodes_states[hn];
            && s in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys
            && vp in hn_state.block_consensus_engine_state.block_slashing_db_hist[s]            
        ensures ( exists duty, db, randao_reveal ::
                    && var hn_state := dv.honest_nodes_states[hn];
                    && inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_proposer_duty_and_randao_reveal_body(dv, hn, s, db, duty, vp, randao_reveal) 
                )                
        {
            var hn_state := dv.honest_nodes_states[hn];            
            assert inv_exists_db_in_block_slashing_db_hist_and_proposer_duty_and_randao_reveal_for_every_validity_predicate_body(hn_state);
            assert s in hn_state.block_consensus_engine_state.block_slashing_db_hist.Keys;
            assert vp in hn_state.block_consensus_engine_state.block_slashing_db_hist[s].Keys;

            assert ( exists db: set<SlashingDBBlock>, duty: ProposerDuty, randao_reveal: BLSSignature ::
                        && duty.slot == s
                        && db in hn_state.block_consensus_engine_state.block_slashing_db_hist[s][vp]
                        && vp == (bb: BeaconBlock) => ci_decision_is_valid_beacon_block(db, bb, duty, randao_reveal)
                    );

            var db: set<SlashingDBBlock>, duty: ProposerDuty, randao_reveal: BLSSignature :|
                        && duty.slot == s
                        && db in hn_state.block_consensus_engine_state.block_slashing_db_hist[s][vp]
                        && vp == (bb: BeaconBlock) => ci_decision_is_valid_beacon_block(db, bb, duty, randao_reveal)
                    ;

            assert inv_sent_vp_is_based_on_existing_slashing_db_and_rcvd_proposer_duty_and_randao_reveal_body(dv, hn, s, db, duty, vp, randao_reveal);
        }
    }   

    lemma lem_inv_available_current_proposer_duty_is_latest_proposer_duty(
        dv: DVState
    )    
    requires inv_available_current_proposer_duty_is_latest_proposer_duty(dv)    
    ensures inv_available_current_proposer_duty_is_latest_proposer_duty(dv)    
    {}

    lemma lem_construct_complete_signed_block_assumptions_helper(
        dv: DVState
    )    
    requires inv_only_dv_construct_complete_signing_functions(dv)    
    ensures construct_complete_signed_block_assumptions_helper(
                dv.construct_complete_signed_block,
                dv.dv_pubkey,
                dv.all_nodes
            )  
    {}

    lemma lem_inv_active_proposer_consensus_instances_keys_is_subset_of_block_slashing_db_hist(
        dv: DVState
    )    
    requires inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist(dv)    
    ensures  inv_active_consensus_instances_on_beacon_blocks_are_tracked_in_block_slashing_db_hist(dv)
    {}   

    lemma lem_inv_rcvd_block_shares_are_from_sent_messages_inv_rcvd_block_shares_are_in_all_sent_messages(
        dv: DVState
    )    
    requires inv_rcvd_block_shares_are_from_sent_messages(dv)    
    ensures  inv_rcvd_block_shares_are_in_all_sent_messages(dv)
    {}

    lemma lem_inv_block_shares_to_broadcast_are_sent_messages_inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(
        dv: DVState
    )
    requires inv_block_shares_to_broadcast_are_sent_messages(dv)
    ensures inv_block_shares_to_broadcast_is_a_subset_of_all_sent_messages(dv)
    {}  

    lemma lem_inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k_inv_active_proposer_consensus_instances_predicate_is_in_block_slashing_db_hist(dv: DVState)    
    requires inv_current_validity_predicate_for_slot_k_is_stored_in_block_slashing_db_hist_k(dv)
    ensures inv_constraints_on_active_consensus_instances_on_beacon_blocks_are_ensured_with_block_slashing_db_hist(dv)
    {}  


    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // lemma lem_inv_proposer_duty_in_next_delivery_is_not_lower_than_latest_served_proposer_duty_ind_inv(
    //     dv: DVState
    // )         
    // requires inv_all_honest_nodes_is_a_quorum(dv)      
    // requires inv_latest_served_duty_is_a_rcvd_duty(dv)    
    // requires inv_proposer_duty_in_next_delivery_is_not_lower_than_rcvd_proposer_duties(dv)
    // ensures inv_proposer_duty_in_next_delivery_is_not_lower_than_latest_served_proposer_duty(dv)
    // {   
    //     var queue := dv.sequence_proposer_duties_to_be_served;
    //     var index := dv.index_next_proposer_duty_to_be_served;        
    //     var next_duty := queue[index].proposer_duty;
    //     var hn := queue[index].node;

    //     if hn in dv.honest_nodes_states.Keys 
    //     {
    //         var dvc := dv.honest_nodes_states[hn];
    //         if dvc.latest_proposer_duty.isPresent()
    //         {
    //             var duty := dvc.latest_proposer_duty.safe_get();
    //             assert duty in dvc.all_rcvd_duties;  
    //             assert duty.slot <= next_duty.slot;  
    //         }
    //     }
    // } 
    
}