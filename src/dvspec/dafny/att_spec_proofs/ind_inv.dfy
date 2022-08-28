include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"

module AttInductiveInvariants
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened AttInvariants

    predicate att_ind_inv<D(!new, 0)>(dvn: DVState)
    {
        && forall i: Slot :: no_conflict_decisions_pred1_in_sec_3_1(dvn.consensus_on_attestation_data[i])
        && forall i: Slot :: no_decisions_pred2_in_sec_3_1(dvn.consensus_on_attestation_data[i])
        && consistant_att_slashing_databases_between_honest_nodes_pred3_in_sec_3_2<D>(dvn)
        && consistant_attestations_in_one_slashing_db_pred4_in_sec_3_2<D>(dvn)
        && curr_att_duty_is_last_served_duty_pred5_in_sec_3_3<D>(dvn)       
        && exisiting_consensus_instance_for_curr_att_duty_pred6_in_sec_3_3<D>(dvn)       
        && active_consensus_instances_imples_existence_of_curr_att_duty_pred7_in_sec_3_3<D>(dvn)       
        && queued_duties_later_than_curr_att_duty_pred8_in_sec_3_3<D>(dvn)       
        && submitted_att_by_curr_att_duty_pred9_in_sec_3_3<D>(dvn)       
        && none_latest_att_duty_implies_empty_att_duty_queue_pred10_in_sec_3_4<D>(dvn)       
        && queued_duties_later_than_latest_att_duty_pred11_in_sec_3_4<D>(dvn)       
        && submitted_att_by_latest_att_duty_pred12_in_sec_3_4<D>(dvn)       
        && active_consensus_instances_for_slots_until_latest_att_duty_pred13_in_sec_3_4<D>(dvn)       
        && no_active_consensus_instances_for_queued_att_duties_pred14_in_sec_3_5<D>(dvn)       
        && att_from_imported_block_is_decided_value_pred16_in_sec_3_6<D>(dvn)       
        && old_duty_has_submitted_att_data_pred17_in_sec_3_6<D>(dvn)       
        && AttConsensusDecided_is_decided_value_pred18_in_sec_3_7<D>(dvn)       
        && local_active_consensus_instance_not_later_than_latest_duty_pred19a_in_sec_3_7<D>(dvn)       
        && no_latest_duty_is_older_than_distributed_undecided_consensus_instance_pred19b_in_sec_3_7<D>(dvn)       
        && strictly_monotonic_att_duties_queue_pred20_in_sec_3_7<D>(dvn)       
        && constructable_set_of_att_shares_has_at_least_one_share_from_honest_node_pred21_in_sec_3_7<D>(dvn)       
        && no_missing_att_in_db_pred22_in_sec_3_7<D>(dvn)       
        && no_missing_att_in_db_pred23_in_sec_3_7<D>(dvn)       
        && pred24<D>(dvn)
        && pred25_in_sec_3_7<D>(dvn)  
        && sent_att_share_from_honest_node_pred26_in_sec_3_7<D>(dvn)       
        && undecided_dist_consensus_instance_implies_latest_att_duty_pred27_in_sec_3_7<D>(dvn)       
        && at_most_one_undecided_dist_consensus_instance_pred28_in_sec_3_7<D>(dvn)       
        && shared_rcvd_att_duties_pred29_in_sec_3_7<D>(dvn)      
        && same_function_to_reconstruct_attestations_pred30_in_sec_3_7<D>(dvn) 
    }
    



/*
    predicate fixed_set_all_nodes_in_sec_3_7<D(!new, 0)>(
        s: DVCNodeState, 
        e: Types.Event,
        s': DVCNodeState)
    requires f_process_event.requires(s, e)
    {
        s' == DVCNode_Spec.f_process_event(s, e).state ==> s.peers == s'.peers                
    }
    */
}