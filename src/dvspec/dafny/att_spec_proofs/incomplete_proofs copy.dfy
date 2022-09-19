include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"
include "../att_spec_proofs/fnc_inv.dfy"
include "../att_spec_proofs/dvn_next_invs_1_7.dfy"
include "../att_spec_proofs/dvn_next_invs_8_18.dfy"
include "../att_spec_proofs/helper_sets_lemmas.dfy"


module Incomplete_Proofs 
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB    
    import opened Helper_Sets_Lemmas
    import opened DVN_Next_Invs_1_7
    import opened DVN_Next_Invs_8_18
    import opened Fnc_Inv    

    lemma {:axiom} axiom_inv19(dvc: DVCNodeState)    
    ensures inv19_body(dvc)

    

     
    
    /*

    

    lemma lemma_inv19_f_check_for_next_queued_duty(
        process: DVCNodeState,
        process': DVCNodeState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state        
    requires inv19_body(process)    
    // ensures inv19_body(process')
    decreases process.attestation_duties_queue
    {
        if  && process.attestation_duties_queue != [] 
            && (
                || process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided
                || !process.current_attestation_duty.isPresent()
            )    
        {            
                if process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided.Keys 
                {
                    var queue_head := process.attestation_duties_queue[0];
                    var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, process.future_att_consensus_instances_already_decided[queue_head.slot]);
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..],
                        future_att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided - {queue_head.slot},
                        attestation_slashing_db := new_attestation_slashing_db,
                        attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                            process.attestation_consensus_engine_state,
                            new_attestation_slashing_db
                        )                        
                    );
                    assert inv9_body(process_mod);
                    lemma_inv19_f_check_for_next_queued_duty(process_mod, process');
                }
                else
                { 
                    var next_duty := process.attestation_duties_queue[0];
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    );     

                    assert forall queued_duty: AttestationDuty | 
                                queued_duty in process_mod.attestation_duties_queue ::
                                    next_duty.slot <= queued_duty.slot;

                    assert inv19_body(process_mod);
                    lemma_inv19_f_start_next_duty(process_mod, next_duty, process');
                }
        }
        else
        {  }
    }

    lemma lemma_inv19_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        process': DVCNodeState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv19_body(process)
    ensures inv19_body(process')
    {
        var process_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );  

        if process.latest_attestation_duty.isPresent() 
        {
            assert process_mod.latest_attestation_duty.isPresent();
            assert process.latest_attestation_duty.safe_get()
                        == process_mod.latest_attestation_duty.safe_get();
            assert process.latest_attestation_duty.safe_get().slot <= attestation_duty.slot;
            assert process_mod.latest_attestation_duty.safe_get().slot <= attestation_duty.slot;            
            assert inv19_body(process_mod);      
        }
        else 
        {
            assert !process_mod.latest_attestation_duty.isPresent();              
            assert inv19_body(process_mod);      
        }
        
        lemma_inv19_f_check_for_next_queued_duty(process_mod, process');        
    } 

    */

    lemma {:axiom} axiom_inv4(dvn: DVState)    
    ensures inv4(dvn) 
     
     /*
    // It takes more than 60 seconds to prove lemma_inv4_dvn_next.
    lemma lemma_inv4_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )
    requires inv1(dvn)    
    requires NextEvent(dvn, event, dvn')
    requires inv4(dvn)
    ensures inv4(dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(att_duty) =>     
                        axiom_inv4(dvn');                    
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        axiom_inv4(dvn');
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
                        axiom_inv4(dvn');
   
                    case ImportedNewBlock(block) => 
                        axiom_inv4(dvn');                        
                                                
                    case ResendAttestationShares =>                         
                        

                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }        
    }   
    */

/*
    lemma lemma_inv4_dvn_next(
        dvn: DVState,
        event: DV.Event,
        dvn': DVState
    )
    requires inv1(dvn)    
    requires NextEvent(dvn, event, dvn')
    requires inv4(dvn)
    ensures inv4(dvn')
    {        
        match event 
        {
            case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) =>
                var dvc := dvn.honest_nodes_states[node];
                var dvc' := dvn'.honest_nodes_states[node];
                match nodeEvent
                {
                    case ServeAttstationDuty(att_duty) =>     
                        assert dvn'.index_next_attestation_duty_to_be_served 
                                    == dvn.index_next_attestation_duty_to_be_served + 1;
                        forall hn | hn in dvn'.honest_nodes_states.Keys                          
                        ensures inv4_body( hn, 
                                           dvn'.honest_nodes_states[hn].all_rcvd_duties, 
                                           dvn'.sequence_attestation_duties_to_be_served,
                                           dvn'.index_next_attestation_duty_to_be_served
                                         )
                        {
                            if hn != node 
                            {
                                assert dvn'.honest_nodes_states[hn] == dvn.honest_nodes_states[hn];
                                assert inv4_body( hn, 
                                                  dvn'.honest_nodes_states[hn].all_rcvd_duties,
                                                  dvn'.sequence_attestation_duties_to_be_served,
                                                  dvn'.index_next_attestation_duty_to_be_served);
                            }
                            else 
                            {      
                                var duty_and_node := dvn.sequence_attestation_duties_to_be_served[
                                                            dvn.index_next_attestation_duty_to_be_served
                                                        ];
                                var attestation_duty := duty_and_node.attestation_duty;
                                var len := dvn'.index_next_attestation_duty_to_be_served;
                                var seq_att_duties := dvn'.sequence_attestation_duties_to_be_served;

                                assert f_serve_attestation_duty.requires(dvc, attestation_duty);
                                assert dvc' == f_serve_attestation_duty(dvc, attestation_duty).state;

                                assert && len > 0;
                                       && var index := len - 1;
                                       && attestation_duty == seq_att_duties[index].attestation_duty
                                       && node == seq_att_duties[index].node;
                                /*
    requires inv4_body(hn, dvc.all_rcvd_duties, seq_att_duties, len)    
    
             */
                                                        /*
                                lemma_inv4_f_serve_attestation_duty(
                                    dvc, duty_and_node.attestation_duty, dvc',
                                    node,
                                    dvn'.sequence_attestation_duties_to_be_served,
                                    dvn'.index_next_attestation_duty_to_be_served
                                );                        
                                */     
                                axiom_inv4(dvn');                                                   
                            }
                        }                        
                        
                    case AttConsensusDecided(id, decided_attestation_data) => 
                        lemma_inv4_f_att_consensus_decided(
                            dvc, id, decided_attestation_data, dvc',
                            node, 
                            dvn'.sequence_attestation_duties_to_be_served, 
                            dvn'.index_next_attestation_duty_to_be_served);                                            
                        
                    case ReceviedAttesttionShare(attestation_share) =>                         
                        lemma_inv4_f_listen_for_attestation_shares(
                            dvc, attestation_share, dvc',
                            node, 
                            dvn'.sequence_attestation_duties_to_be_served, 
                            dvn'.index_next_attestation_duty_to_be_served);                                            
   
                    case ImportedNewBlock(block) => 
                        /*
                        var dvc_mod := add_block_to_bn(dvc, nodeEvent.block);
                        
                        lemma_inv4_add_block_to_bn(
                            dvc, nodeEvent.block, dvc_mod,
                            node,
                            dvn.sequence_attestation_duties_to_be_served, 
                            dvn.index_next_attestation_duty_to_be_served);

                        lemma_inv4_f_listen_for_new_imported_blocks(
                            dvc_mod, block, dvc',
                            node,
                            dvn.sequence_attestation_duties_to_be_served, 
                            dvn.index_next_attestation_duty_to_be_served);
                            */
                        axiom_inv4(dvn');
                                             
                    case ResendAttestationShares =>                         
                        
                    case NoEvent => 
                        
                }

            case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) =>
                
        }        
    }  

    lemma lemma_inv4_f_serve_attestation_duty(
        dvc: DVCNodeState,
        attestation_duty: AttestationDuty,
        dvc': DVCNodeState, 
        hn: BLSPubkey,
        seq_att_duties: iseq<AttestationDutyAndNode>,
        len: nat 
    )  
    requires f_serve_attestation_duty.requires(dvc, attestation_duty)
    requires dvc' == f_serve_attestation_duty(dvc, attestation_duty).state
    requires inv4_body(hn, dvc.all_rcvd_duties, seq_att_duties, len)    
    requires && len > 0
             && var index := len - 1;
             && attestation_duty == seq_att_duties[index].attestation_duty
             && hn == seq_att_duties[index].node
    // ensures dvc'.all_rcvd_duties == dvc.all_rcvd_duties + {attestation_duty}    
    // ensures inv4_body(hn, dvc'.all_rcvd_duties, seq_att_duties, len)    
    {
        var dvc_mod := dvc.(
                attestation_duties_queue := dvc.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := dvc.all_rcvd_duties + {attestation_duty}
            ); 
        
        var index := len - 1;
        assert 0 <= index < len;
        assert attestation_duty == seq_att_duties[index].attestation_duty;

        assert inv4_body(hn, dvc_mod.all_rcvd_duties, seq_att_duties, len);       

        /*
        forall duty: AttestationDuty | duty in dvc_mod.all_rcvd_duties 
        ensures exists k: nat :: (  && 0 <= k < len
                                    && seq_att_duties[k].node == hn
                                    && seq_att_duties[k].attestation_duty == duty
                                 )
        {
            if (duty == attestation_duty)
            {
                var index := len - 1;
                assert attestation_duty == seq_att_duties[index].attestation_duty;
            }
            else 
            {
                assert duty in dvc.all_rcvd_duties;
            }
        }
        
        assert inv4_body(hn, dvc_mod.all_rcvd_duties, seq_att_duties, len);       

        lemma_inv4_f_check_for_next_queued_duty(dvc_mod, dvc', hn, seq_att_duties, len);        
        */
    }

    

      

    /*


    

     


    lemma lemma_inv4_add_block_to_bn(        
        s: DVCNodeState,
        block: BeaconBlock,
        s': DVCNodeState, 
        hn: BLSPubkey,
        seq_att_duties: iseq<AttestationDutyAndNode>,
        len: nat 
    )
    requires add_block_to_bn.requires(s, block)
    requires s' == add_block_to_bn(s, block)    
    requires inv4_body(hn, s.all_rcvd_duties, seq_att_duties, len)
    requires inv4_body(hn, s'.all_rcvd_duties, seq_att_duties, len)
    { } 

    lemma lemma_inv4_f_listen_for_attestation_shares(
        process: DVCNodeState,
        attestation_share: AttestationShare,
        process': DVCNodeState, 
        hn: BLSPubkey,
        seq_att_duties: iseq<AttestationDutyAndNode>,
        len: nat 
    )
    requires f_listen_for_attestation_shares.requires(process, attestation_share)
    requires process' == f_listen_for_attestation_shares(process, attestation_share).state
    requires inv4_body(hn, process.all_rcvd_duties, seq_att_duties, len)
    ensures inv4_body(hn, process'.all_rcvd_duties, seq_att_duties, len)
    { 
        assert process'.all_rcvd_duties == process.all_rcvd_duties;
    }

    lemma lemma_inv4_f_start_next_duty(
            dvc: DVCNodeState, 
            attestation_duty: AttestationDuty, 
            dvc': DVCNodeState,
            hn: BLSPubkey,
            seq_att_duties: iseq<AttestationDutyAndNode>,
            len: nat )
    requires f_start_next_duty.requires(dvc, attestation_duty)
    requires dvc' == f_start_next_duty(dvc, attestation_duty).state
    requires inv4_body(hn, dvc.all_rcvd_duties, seq_att_duties, len)
    ensures inv4_body(hn, dvc'.all_rcvd_duties, seq_att_duties, len)
    {  
        assert dvc'.all_rcvd_duties == dvc.all_rcvd_duties;
    }

    lemma lemma_inv4_f_att_consensus_decided(
        process: DVCNodeState,
        id: Slot,
        decided_attestation_data: AttestationData, 
        process': DVCNodeState, 
        hn: BLSPubkey,
        seq_att_duties: iseq<AttestationDutyAndNode>,
        len: nat 
    )
    requires f_att_consensus_decided.requires(process, id, decided_attestation_data)
    requires process' == f_att_consensus_decided(process, id, decided_attestation_data).state 
    requires inv4_body(hn, process.all_rcvd_duties, seq_att_duties, len)
    ensures inv4_body(hn, process'.all_rcvd_duties, seq_att_duties, len)
    {
        
        var local_current_attestation_duty := process.current_attestation_duty.safe_get();
        var attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);

        var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
        var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
        var attestation_signature_share := rs_sign_attestation(decided_attestation_data, fork_version, attestation_signing_root, process.rs);
        var attestation_with_signature_share := AttestationShare(
                aggregation_bits := get_aggregation_bits(local_current_attestation_duty.validator_index),
                data := decided_attestation_data, 
                signature := attestation_signature_share
            ); 

        var process_mod := 
            process.(
                current_attestation_duty := None,
                attestation_shares_to_broadcast := process.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                attestation_slashing_db := attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    process.attestation_consensus_engine_state,
                    attestation_slashing_db
                )
            );

        var ret_check_for_next_queued_duty := f_check_for_next_queued_duty(process_mod);
        
        lemma_inv4_f_check_for_next_queued_duty(process_mod, ret_check_for_next_queued_duty.state, hn, seq_att_duties, len);

        assert process' == ret_check_for_next_queued_duty.state;
        
    }  

    lemma lemma_inv4_f_check_for_next_queued_duty(
        dvc: DVCNodeState,
        dvc': DVCNodeState, 
        hn: BLSPubkey,
        seq_att_duties: iseq<AttestationDutyAndNode>,
        len: nat 
    )
    requires f_check_for_next_queued_duty.requires(dvc)
    requires dvc' == f_check_for_next_queued_duty(dvc).state
    requires inv4_body(hn, dvc.all_rcvd_duties, seq_att_duties, len)
    ensures inv4_body(hn, dvc'.all_rcvd_duties, seq_att_duties, len)
    decreases dvc.attestation_duties_queue
    {
        if  && dvc.attestation_duties_queue != [] 
            && (
                || dvc.attestation_duties_queue[0].slot in dvc.future_att_consensus_instances_already_decided
                || !dvc.current_attestation_duty.isPresent()
            )    
        {            
                if dvc.attestation_duties_queue[0].slot in dvc.future_att_consensus_instances_already_decided.Keys 
                {
                    var queue_head := dvc.attestation_duties_queue[0];
                    var new_attestation_slashing_db := f_update_attestation_slashing_db(dvc.attestation_slashing_db, dvc.future_att_consensus_instances_already_decided[queue_head.slot]);
                    var dvc_mod := dvc.(
                        attestation_duties_queue := dvc.attestation_duties_queue[1..],
                        future_att_consensus_instances_already_decided := dvc.future_att_consensus_instances_already_decided - {queue_head.slot},
                        attestation_slashing_db := new_attestation_slashing_db,
                        attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                            dvc.attestation_consensus_engine_state,
                            new_attestation_slashing_db
                        )                        
                    );
                    assert inv4_body(hn, dvc_mod.all_rcvd_duties, seq_att_duties, len);
                    lemma_inv4_f_check_for_next_queued_duty(dvc_mod, dvc', hn, seq_att_duties, len);
                }
                else
                { 
                    var dvc_mod := dvc.(
                        attestation_duties_queue := dvc.attestation_duties_queue[1..]
                    );         
                    assert inv4_body(hn, dvc_mod.all_rcvd_duties, seq_att_duties, len);
                    lemma_inv4_f_start_next_duty(dvc_mod, dvc.attestation_duties_queue[0], dvc', hn, seq_att_duties, len);
                }
        }
        else
        { 
            assert dvc'.all_rcvd_duties == dvc.all_rcvd_duties;
        }
    }

    lemma lemma_inv4_f_listen_for_new_imported_blocks(
        process: DVCNodeState,
        block: BeaconBlock,
        process': DVCNodeState,
        hn: BLSPubkey,
        seq_att_duties: iseq<AttestationDutyAndNode>,
        len: nat 
    )
    requires f_listen_for_new_imported_blocks.requires(process, block)
    requires process' == f_listen_for_new_imported_blocks(process, block).state
    requires inv4_body(hn, process.all_rcvd_duties, seq_att_duties, len)
    ensures inv4_body(hn, process'.all_rcvd_duties, seq_att_duties, len)
    {
        var new_consensus_instances_already_decided := f_listen_for_new_imported_blocks_helper_1(process, block);

        var att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            f_listen_for_new_imported_blocks_helper_2(process, att_consensus_instances_already_decided);

        var process :=
                process.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := stopConsensusInstances(
                                    process.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := process.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := process.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );    

        assert inv4_body(hn, process.all_rcvd_duties, seq_att_duties, len);                

        if process.current_attestation_duty.isPresent() && process.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
        {
            var decided_attestation_data := att_consensus_instances_already_decided[process.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data);
            var process := process.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                    process.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );

            assert inv4_body(hn, process.all_rcvd_duties, seq_att_duties, len);
            
            lemma_inv4_f_check_for_next_queued_duty(process, process', hn, seq_att_duties, len);
        }
        else
        {}
    }  
    */
}