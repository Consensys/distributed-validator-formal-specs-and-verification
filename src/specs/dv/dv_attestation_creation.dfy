include "../../common/commons.dfy"
include "../../proofs/no_slashable_attestations/common/dvc_attestation_creation_instrumented.dfy"
include "../consensus/consensus.dfy"
include "../dvc/consensus_engine.dfy"
include "../network/network.dfy"
include "../../proofs/bn_axioms.dfy"
include "../../proofs/rs_axioms.dfy"

module Att_DV 
{
    import opened Types
    import opened Common_Functions
    import opened Signing_Methods
    import opened Network_Spec
    import opened Consensus
    import opened Consensus_Engine
    import opened Att_DVC
    import opened BN_Axioms
    import opened RS_Axioms
    import opened Att_DV_Assumptions

    predicate dvcs_are_initialized_with_empty_beacon_nodes(
        s: AttDVState,
        initial_attestation_slashing_db: set<SlashingDBAttestation>
    )
    {
        && ( forall n | n in s.honest_nodes_states.Keys ::
                Att_DVC.init(s.honest_nodes_states[n], s.dv_pubkey, s.all_nodes, s.construct_signed_attestation_signature, initial_attestation_slashing_db, n)
            )   
        && ( forall n | n in s.honest_nodes_states.Keys ::
                |s.honest_nodes_states[n].bn.submitted_data| == 0    
            )   
    }

    predicate consensus_instances_are_initialized_with_no_decision_values(
        s: AttDVState
    )
    {
        &&  ( forall ci | ci in  s.consensus_on_attestation_data.Values ::
                Consensus.init(ci, s.all_nodes, s.honest_nodes_states.Keys)
            )
        && ( forall i: Slot :: i in s.consensus_on_attestation_data 
                            ==> !s.consensus_on_attestation_data[i].decided_value.isPresent()
            )       
    }

    predicate init(
        s: AttDVState,
        initial_attestation_slashing_db: set<SlashingDBAttestation>
    )
    {
        && assump_set_of_byz_nodes(s.dv_pubkey, s.all_nodes, s.honest_nodes_states.Keys, s.adversary.nodes)
        && assump_construction_of_signed_attestation_signatures(
                s.construct_signed_attestation_signature,
                s.dv_pubkey,
                s.all_nodes
            )
        && s.all_attestations_created == {}
        && dvcs_are_initialized_with_empty_beacon_nodes(s, initial_attestation_slashing_db)
        && Network_Spec.init(s.att_network, s.all_nodes)
        && consensus_instances_are_initialized_with_no_decision_values(s)
        && assump_seq_of_att_duties_is_in_order_of_slots(s.sequence_of_attestation_duties_to_be_served)
        && s.index_next_attestation_duty_to_be_served == 0   
    }

    predicate valid_Block(
        dv: AttDVState,
        process: AttDVCState,
        block: BeaconBlock
    )
    requires block.body.state_root in process.bn.state_roots_of_imported_blocks
    {
        var valIndex := af_bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);
        && ( forall a1, a2 | 
                && a1 in block.body.attestations
                && Non_Instr_Att_DVC.has_correct_validator_index(a1, process.bn, block, valIndex)
                && a2 in block.body.attestations
                && Non_Instr_Att_DVC.has_correct_validator_index(a2, process.bn, block, valIndex)                        
                ::
                a1.data.slot == a2.data.slot ==> a1 == a2  
            )      
        && any_of_our_attestations_in_the_block_has_been_previously_sent(dv, process, block)
    }      

    predicate valid_ServeAttestationDuty_and_ImportedNewBlock_events(
        s: AttDVState,
        node: BLSPubkey,
        nodeEvent: AttestationEvent
    )
    requires node in s.honest_nodes_states.Keys
    requires nodeEvent.ImportedNewBlock? ==> nodeEvent.block.body.state_root in s.honest_nodes_states[node].bn.state_roots_of_imported_blocks
    {
            && ( nodeEvent.ServeAttestationDuty? ==>
                    && var attestation_duty_to_be_served := s.sequence_of_attestation_duties_to_be_served[s.index_next_attestation_duty_to_be_served];
                    && node == attestation_duty_to_be_served.node 
                    && nodeEvent.attestation_duty == attestation_duty_to_be_served.attestation_duty
                )
            && ( nodeEvent.ImportedNewBlock? ==>
                    valid_Block(s, s.honest_nodes_states[node], nodeEvent.block)
                )
    }    

    predicate valid_HonestNodeTakingStep_event(
        s: AttDVState,
        event: DVAttestationEvent
    )
    {
        event.HonestNodeTakingStep? ==>
            (
                &&  var nodeEvent := event.event;
                &&  event.node in s.honest_nodes_states.Keys
                &&  valid_ServeAttestationDuty_and_ImportedNewBlock_events(
                        f_add_block_to_bn_if_ImportedNewBlock_event(s, event.node, event.event),
                        event.node,
                        event.event
                    )
            )  
    }       

    predicate next_preconditions(
        s: AttDVState
    )
    {
        forall e :: valid_HonestNodeTakingStep_event(s, e) ==> next_event_preconditions(s, e)
    }
 
    predicate next(
        s: AttDVState,
        s': AttDVState 
    )
    requires next_preconditions(s)
    {
        exists e ::
            && valid_HonestNodeTakingStep_event(s, e)
            && next_event(s, e, s')
    }

    predicate next_unchanged(dv: AttDVState, dv': AttDVState)
    {
        && dv.all_nodes == dv'.all_nodes
        && dv.adversary == dv'.adversary
        && dv.honest_nodes_states.Keys == dv'.honest_nodes_states.Keys        
        && dv.dv_pubkey == dv'.dv_pubkey
        && dv.construct_signed_attestation_signature
                == dv'.construct_signed_attestation_signature
        && dv.sequence_of_attestation_duties_to_be_served
                == dv'.sequence_of_attestation_duties_to_be_served
        && ( forall n | n in dv'.honest_nodes_states.Keys :: 
                var nodes' := dv'.honest_nodes_states[n];
                && nodes'.construct_signed_attestation_signature == dv'.construct_signed_attestation_signature
                && nodes'.dv_pubkey == dv.dv_pubkey       
                && nodes'.peers == dv.all_nodes
        )
    }

    predicate att_signature_is_signed_with_pubkey(
        a: Attestation,
        pubkey: BLSPubkey
    )
    {
        && var fork_version := af_bn_get_fork_version(compute_start_slot_at_epoch(a.data.target.epoch));
        && var attestation_signing_root := compute_attestation_signing_root(a.data, fork_version);      
        && verify_bls_signature(attestation_signing_root, a.signature, pubkey)  
    }    

      // TODO: Modify has_correct_validator_index to include the entirety the forall premise 
    predicate any_of_our_attestations_in_the_block_has_been_previously_sent(
        dv: AttDVState,
        new_p: AttDVCState,
        block: BeaconBlock
    )
    requires block.body.state_root in new_p.bn.state_roots_of_imported_blocks
    {
        var valIndex := af_bn_get_validator_index(new_p.bn, block.body.state_root, new_p.dv_pubkey);
        forall a |  
            && a in block.body.attestations 
            && Non_Instr_Att_DVC.has_correct_validator_index(
                    a,
                    new_p.bn,
                    block,
                    valIndex
                )
            ::
            exists a' 
                ::
                && a' in dv.all_attestations_created
                && a'.data == a.data 
                && att_signature_is_signed_with_pubkey(a', dv.dv_pubkey)    
    }        
   
    predicate next_honest_node_event_preconditions(
        s: AttDVCState,
        event: AttestationEvent
    )
    {
        match event 
            case ServeAttestationDuty(attestation_duty) => 
                && f_serve_attestation_duty.requires(s, attestation_duty)
            case AttConsensusDecided(id, decided_attestation_data) => 
                && f_att_consensus_decided.requires(s, id,  decided_attestation_data)
            case ReceivedAttestationShare(attestation_share) => 
                f_listen_for_attestation_shares.requires(s, attestation_share)
            case ImportedNewBlock(block) => 
                f_listen_for_new_imported_blocks.requires(s, block)
            case ResendAttestationShares => 
                f_resend_attestation_shares.requires(s) 
            case NoEvent => 
                true       
    }

    function f_add_block_to_bn(
        s: AttDVCState,
        block: BeaconBlock
    ): AttDVCState
    { 
        s.(
            bn := s.bn.(
                state_roots_of_imported_blocks := s.bn.state_roots_of_imported_blocks + {block.body.state_root}
            )
        )
    }    

    function f_add_block_to_bn_if_ImportedNewBlock_event(
        s: AttDVState,
        node: BLSPubkey,
        nodeEvent: AttestationEvent
    ): AttDVState
    requires node in s.honest_nodes_states.Keys
    {
        if nodeEvent.ImportedNewBlock? then 
            s.(
                honest_nodes_states := s.honest_nodes_states[node := f_add_block_to_bn(s.honest_nodes_states[node], nodeEvent.block)]
            )
        else 
            s 
                  
    }    

    predicate next_honest_node_event_preconditions_after_adding_block(
        s: AttDVState,
        node: BLSPubkey,
        nodeEvent: AttestationEvent        
    )
    {
        && node in s.honest_nodes_states.Keys
        && next_honest_node_event_preconditions(f_add_block_to_bn_if_ImportedNewBlock_event(s, node, nodeEvent).honest_nodes_states[node], nodeEvent)        
    }

    predicate next_event_preconditions(
        s: AttDVState,
        event: DVAttestationEvent
    )
    {    
        ( event.HonestNodeTakingStep? ==> next_honest_node_event_preconditions_after_adding_block(s, event.node, event.event))      
    }

    predicate next_event(
        s: AttDVState,
        event: DVAttestationEvent,
        s': AttDVState
    )
    requires next_event_preconditions(s, event)  
    {
        && next_unchanged(s, s')
        && (
            match event
                case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) => 
                    next_honest_node(s, node, nodeEvent, nodeOutputs, s')
                case AdversaryTakingStep(node, new_attestation_shares_sent, messagesReceivedByTheNode) => 
                    next_adversary(s, node, new_attestation_shares_sent, messagesReceivedByTheNode, s')
        )
    }

    predicate next_honest_node(
        s: AttDVState,
        node: BLSPubkey,
        nodeEvent: AttestationEvent,
        nodeOutputs:  AttestationOutputs,
        s': AttDVState        
    ) 
    requires next_unchanged(s, s')
    requires next_honest_node_event_preconditions_after_adding_block(s, node, nodeEvent)   
    {
        && node in s.honest_nodes_states.Keys        
        && var s_w_honest_node_states_updated := f_add_block_to_bn_if_ImportedNewBlock_event(s, node, nodeEvent);
        && next_honest_node_after_adding_block_to_bn(s_w_honest_node_states_updated, node, nodeEvent, nodeOutputs, s' )                
    }

    predicate next_consensus_instance(
        s: AttDVState,
        node: BLSPubkey,
        nodeEvent: AttestationEvent,
        nodeOutputs:  AttestationOutputs,
        s': AttDVState
    )
    {
        forall cid | cid in s.consensus_on_attestation_data.Keys ::
            &&  var output := 
                    if nodeEvent.AttConsensusDecided? && nodeEvent.id == cid then 
                        Some(Decided(node, nodeEvent.decided_attestation_data))
                    else
                        None
                    ;
            &&  var validityPredicates := 
                    map n |
                            && n in s.honest_nodes_states.Keys 
                            && cid in s.honest_nodes_states[n].attestation_consensus_engine_state.active_consensus_instances.Keys
                        ::
                            s.honest_nodes_states[n].attestation_consensus_engine_state.active_consensus_instances[cid].validityPredicate
                    ;
            &&  Consensus.next(
                    s.consensus_on_attestation_data[cid],
                    validityPredicates,
                    s'.consensus_on_attestation_data[cid],
                    output
                )
    }

    predicate next_attestation_duty(
        s: AttDVState,
        node: BLSPubkey,
        nodeEvent: AttestationEvent,
        s': AttDVState
    )
    {
        if nodeEvent.ServeAttestationDuty? then
            && var attestation_duty_to_be_served := s.sequence_of_attestation_duties_to_be_served[s.index_next_attestation_duty_to_be_served];
            && node == attestation_duty_to_be_served.node 
            && nodeEvent.attestation_duty == attestation_duty_to_be_served.attestation_duty
            && s'.index_next_attestation_duty_to_be_served == s.index_next_attestation_duty_to_be_served + 1
        else 
            s'.index_next_attestation_duty_to_be_served == s.index_next_attestation_duty_to_be_served
    }

    predicate next_nodes_states(
        s: AttDVState,
        node: BLSPubkey,
        nodeEvent: AttestationEvent,
        nodeOutputs:  AttestationOutputs,
        s': AttDVState
    )
    requires next_unchanged(s, s')
    requires node in s.honest_nodes_states
    requires nodeEvent.ImportedNewBlock? ==> nodeEvent.block.body.state_root in s.honest_nodes_states[node].bn.state_roots_of_imported_blocks
    // requires valid_ServeAttestationDuty_and_ImportedNewBlock_events(s, node, nodeEvent)
    requires next_honest_node_event_preconditions(s.honest_nodes_states[node], nodeEvent)      
    {
        && Att_DVC.next(s.honest_nodes_states[node], nodeEvent, s'.honest_nodes_states[node], nodeOutputs)
        && s'.honest_nodes_states == s.honest_nodes_states[node := s'.honest_nodes_states[node]]
    }

    predicate next_network(
        s: AttDVState,
        node: BLSPubkey,
        nodeEvent: AttestationEvent,
        nodeOutputs:  AttestationOutputs,
        s': AttDVState
    )
    {
        &&  var messagesReceivedByTheNode :=
            match nodeEvent
                case ReceivedAttestationShare(attestation_share) => {attestation_share}
                case _ => {}
            ;
        && Network_Spec.next(s.att_network, s'.att_network, node, nodeOutputs.att_shares_sent, messagesReceivedByTheNode)
    }

    predicate next_honest_node_after_adding_block_to_bn(
        s: AttDVState,
        node: BLSPubkey,
        nodeEvent: AttestationEvent,
        nodeOutputs:  AttestationOutputs,
        s': AttDVState
    )
    requires next_unchanged(s, s')
    requires node in s.honest_nodes_states.Keys 
    requires nodeEvent.ImportedNewBlock? ==> nodeEvent.block.body.state_root in s.honest_nodes_states[node].bn.state_roots_of_imported_blocks
    // requires valid_ServeAttestationDuty_and_ImportedNewBlock_events(s, node, nodeEvent)
    requires next_honest_node_event_preconditions(s.honest_nodes_states[node], nodeEvent)      
    {
        &&  var new_node_state := s'.honest_nodes_states[node];
        
        && s'.all_attestations_created == s.all_attestations_created + nodeOutputs.submitted_data
        && next_attestation_duty(s, node, nodeEvent, s')
        && next_nodes_states(s, node, nodeEvent, nodeOutputs, s')
        && next_network(s, node, nodeEvent, nodeOutputs, s')      
        && next_consensus_instance(s, node, nodeEvent, nodeOutputs, s')      
        && s'.adversary == s.adversary
    }    

    predicate are_valid_new_submitted_aggregated_attestations(
        s: AttDVState,
        s': AttDVState
    )
    {
        && var new_aggregated_attestations_sent := s'.all_attestations_created - s.all_attestations_created;
        && forall aggregated_attestation_sent | aggregated_attestation_sent in new_aggregated_attestations_sent ::
                exists attestation_shares ::
                        && attestation_shares <= s'.att_network.allMessagesSent
                        && var constructed_sig := s.construct_signed_attestation_signature(attestation_shares);
                        && constructed_sig.isPresent()
                        && constructed_sig.safe_get() == aggregated_attestation_sent.signature
                        && all_att_shares_have_same_data(attestation_shares, aggregated_attestation_sent.data)
    }

    predicate are_valid_new_attestation_shares(
        s: AttDVState,
        new_attestation_shares_sent: set<MessaageWithRecipient<AttestationShare>>,
        s': AttDVState
    )
    {
        forall new_attestation_share_sent, signer | new_attestation_share_sent in new_attestation_shares_sent ::
                var fork_version := af_bn_get_fork_version(compute_start_slot_at_epoch(new_attestation_share_sent.message.data.target.epoch));
                var attestation_signing_root := compute_attestation_signing_root(new_attestation_share_sent.message.data, fork_version);
                verify_bls_signature(attestation_signing_root, new_attestation_share_sent.message.signature, signer) ==> signer in s.adversary.nodes
    }

    predicate next_adversary(
        s: AttDVState,
        node: BLSPubkey,
        new_attestation_shares_sent: set<MessaageWithRecipient<AttestationShare>>,
        messagesReceivedByTheNode: set<AttestationShare>,
        s': AttDVState
    )
    {
        && node in (s.all_nodes - s.honest_nodes_states.Keys)
        && are_valid_new_attestation_shares(s, new_attestation_shares_sent, s')
        && Network_Spec.next(s.att_network, s'.att_network, node, new_attestation_shares_sent, messagesReceivedByTheNode)
        && s.all_attestations_created <= s'.all_attestations_created        
        && are_valid_new_submitted_aggregated_attestations(s, s')
        && s' == s.( att_network := s'.att_network,
                     all_attestations_created := s'.all_attestations_created
                    )            
    }
}


module Att_DV_Assumptions 
{
    import opened Types
    import opened Common_Functions
    import opened Signing_Methods
    import opened Network_Spec
    import opened Consensus
    import opened Consensus_Engine
    import opened Att_DVC
    import opened BN_Axioms
    import opened RS_Axioms        

    predicate assump_set_of_byz_nodes(
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>,
        honest_nodes: set<BLSPubkey>,
        byz_nodes: set<BLSPubkey>
    )
    {
        && honest_nodes !! byz_nodes !! {dv_pubkey}
        && all_nodes == honest_nodes + byz_nodes
        && honest_nodes != {}
        && |byz_nodes| <= f(|all_nodes|)
    }

    predicate all_att_shares_have_same_data(
        att_shares: set<AttestationShare>,
        data: AttestationData 
    )
    {
        forall att_share | att_share in att_shares ::att_share.data == data
    }

    predicate signer_threshold(
        all_nodes: set<BLSPubkey>,
        att_shares: set<AttestationShare>,
        signing_root: Root
    )
    {
        && var signers := 
                    set signer, att_share | 
                        && att_share in att_shares
                        && signer in all_nodes
                        && verify_bls_signature(signing_root, att_share.signature, signer)
                    ::
                        signer;
        && |signers| >= quorum(|all_nodes|)
        && signers <= all_nodes
    }    

    // Note: Introduce a prefix for assumptions
    predicate assump_construction_of_signed_attestation_signatures_forward(
        construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>
    )    
    {
        forall data: AttestationData, signing_root: Root, att_shares |
            && all_att_shares_have_same_data(att_shares, data)
            && signer_threshold(all_nodes, att_shares, signing_root) 
        ::
            && construct_signed_attestation_signature(att_shares).isPresent()
            && verify_bls_signature(
                signing_root,
                construct_signed_attestation_signature(att_shares).safe_get(),
                dv_pubkey
            )
    }

    predicate assump_construction_of_signed_attestation_signatures_reverse_helper(
        construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>,
        att_shares: set<AttestationShare>,
        data: AttestationData
    )       
    requires construct_signed_attestation_signature(att_shares).isPresent()
    {
        && var fork_version := af_bn_get_fork_version(compute_start_slot_at_epoch(data.target.epoch));
        && var signing_root := compute_attestation_signing_root(data, fork_version);
        && verify_bls_signature(
            signing_root,
            construct_signed_attestation_signature(att_shares).safe_get(),
            dv_pubkey
        )                   
        && all_att_shares_have_same_data(att_shares, data)
        && signer_threshold(all_nodes, att_shares, signing_root) 
    }

    predicate assump_construction_of_signed_attestation_signatures_reverse(
        construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>
    )    
    {
        forall att_shares |
            && construct_signed_attestation_signature(att_shares).isPresent()
        ::
        exists data: AttestationData ::      
            assump_construction_of_signed_attestation_signatures_reverse_helper(
                construct_signed_attestation_signature,
                dv_pubkey,
                all_nodes,
                att_shares,
                data                
            )
    }    

    predicate assump_construction_of_signed_attestation_signatures(
        construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>
    )
    {
        && (                            
            assump_construction_of_signed_attestation_signatures_forward(
                construct_signed_attestation_signature,
                dv_pubkey,
                all_nodes
            )
        )   
        && (
            assump_construction_of_signed_attestation_signatures_reverse(
                construct_signed_attestation_signature,
                dv_pubkey,
                all_nodes
            )
        )
    }    

    predicate assump_seq_of_att_duties_is_in_order_of_slots(sequence_of_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>)
    {
        && (forall i, j | 
                    && 0 <= i < j
                    && sequence_of_attestation_duties_to_be_served[i].node == sequence_of_attestation_duties_to_be_served[j].node 
                ::
                    sequence_of_attestation_duties_to_be_served[i].attestation_duty.slot < sequence_of_attestation_duties_to_be_served[j].attestation_duty.slot
        )       
    }
}