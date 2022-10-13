include "../../common/commons.dfy"
include "../../proofs/no_slashable_attestations/common/attestation_creation_instrumented.dfy"
include "../consensus/consensus.dfy"
include "../network/network.dfy"
include "../../proofs/no_slashable_attestations/common/dvc_spec_axioms.dfy"

module DV 
{
    import opened Types
    import opened CommonFunctions
    import opened NetworkSpec
    import opened ConsensusSpec
    import opened DVC_Spec
    import opened DVC_Externs_Proofs
    import opened DVC_Spec_Axioms
    

    datatype Adversary = Adversary(
        nodes: set<BLSPubkey>  
    )

    datatype AttestationDutyAndNode = AttestationDutyAndNode(
        attestation_duty: AttestationDuty,
        node: BLSPubkey
    )

    datatype DVState = DVState(
        all_nodes: set<BLSPubkey>,
        honest_nodes_states: map<BLSPubkey, DVCState>,
        adversary: Adversary,
        dv_pubkey: BLSPubkey,
        consensus_on_attestation_data: imaptotal<Slot, ConsensusInstance<AttestationData>>,
        att_network: NetworkSpec.Network<AttestationShare>,
        all_attestations_created: set<Attestation>,
        construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>,
        sequence_attestation_duties_to_be_served: iseq<AttestationDutyAndNode>,
        index_next_attestation_duty_to_be_served: nat,

        ghost globally_signed_attestations: set<Attestation>,
        ghost globally_slashing_db_attestations: set<SlashingDBAttestation>,
        ghost all_att_shares: set<AttestationShare>,
        ghost highest_slot_with_dv_signed_att: Optional<Slot>
    )

    datatype Event = 
    | AdeversaryTakingStep(node: BLSPubkey, new_attestation_shares_sent: set<MessaageWithRecipient<AttestationShare>>,
        messagesReceivedByTheNode: set<AttestationShare>)
    | HonestNodeTakingStep(node: BLSPubkey, event: Types.Event, nodeOutputs: DVC_Spec.Outputs)

    predicate do_all_att_shares_have_the_same_data(
        att_shares: set<AttestationShare>,
        data: AttestationData 
    )
    {
    && (forall att_share | att_share in att_shares ::att_share.data == data)            
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
                        && verify_bls_siganture(signing_root, att_share.signature, signer)
                    ::
                        signer;
        && |signers| >= quorum(|all_nodes|)
           
    }    

    predicate construct_signed_attestation_signature_assumptions_helper_forward(
        construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>
    )    
    {
        forall data: AttestationData, signing_root: Root, att_shares |
            && do_all_att_shares_have_the_same_data(att_shares, data)
            && signer_threshold(all_nodes, att_shares, signing_root) 
        ::
            && construct_signed_attestation_signature(att_shares).isPresent()
            && verify_bls_siganture(
                signing_root,
                construct_signed_attestation_signature(att_shares).safe_get(),
                dv_pubkey
            )
    }

    predicate construct_signed_attestation_signature_assumptions_helper_reverse_helper(
        construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>,
        att_shares: set<AttestationShare>,
        data: AttestationData
    )       
    requires construct_signed_attestation_signature(att_shares).isPresent()
    {
        && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(data.target.epoch));
        && var signing_root := compute_attestation_signing_root(data, fork_version);
        && verify_bls_siganture(
            signing_root,
            construct_signed_attestation_signature(att_shares).safe_get(),
            dv_pubkey
        )                   
        && do_all_att_shares_have_the_same_data(att_shares, data)
        && signer_threshold(all_nodes, att_shares, signing_root) 
    }

    predicate construct_signed_attestation_signature_assumptions_helper_reverse(
        construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>
    )    
    {
        forall att_shares |
            && construct_signed_attestation_signature(att_shares).isPresent()
        ::
        exists data: AttestationData ::      
            construct_signed_attestation_signature_assumptions_helper_reverse_helper(
                construct_signed_attestation_signature,
                dv_pubkey,
                all_nodes,
                att_shares,
                data                
            )
    }    

    predicate construct_signed_attestation_signature_assumptions_helper(
        construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>
    )
    {
        && (                            
            construct_signed_attestation_signature_assumptions_helper_forward(
                construct_signed_attestation_signature,
                dv_pubkey,
                all_nodes
            )
        )   
        && (
            construct_signed_attestation_signature_assumptions_helper_reverse(
                construct_signed_attestation_signature,
                dv_pubkey,
                all_nodes
            )
        )
    }

    predicate construct_signed_attestation_signature_assumptions(
        s: DVState
    )
    {
        construct_signed_attestation_signature_assumptions_helper(
            s.construct_signed_attestation_signature,
            s.dv_pubkey,
            s.all_nodes
        ) 
    }
    
    predicate Init(
        s: DVState,
        initial_attestation_slashing_db: set<SlashingDBAttestation>
    )
    {
        && s.honest_nodes_states.Keys !! s.adversary.nodes !! {s.dv_pubkey}
        && s.all_nodes == s.honest_nodes_states.Keys + s.adversary.nodes
        && s.honest_nodes_states.Keys != {}
        && |s.adversary.nodes| <= f(|s.all_nodes|)
        && construct_signed_attestation_signature_assumptions(s)

        && s.all_attestations_created == {}
        && (
            forall n | n in s.honest_nodes_states.Keys ::
                DVC_Spec.Init(s.honest_nodes_states[n], s.dv_pubkey, s.all_nodes, s.construct_signed_attestation_signature, initial_attestation_slashing_db, n)
        )      
        &&  NetworkSpec.Init(s.att_network, s.all_nodes)
        &&  (
            forall ci | ci in  s.consensus_on_attestation_data.Values ::
                ConsensusSpec.Init(ci, s.all_nodes, s.honest_nodes_states.Keys)
        )
        && (forall i: Slot :: i in s.consensus_on_attestation_data 
                            ==> !s.consensus_on_attestation_data[i].decided_value.isPresent()
        )        
        && is_sequence_attestation_duties_to_be_served_orderd(s)
        && s.index_next_attestation_duty_to_be_served == 0   
        // //
        && ( forall n | n in s.honest_nodes_states.Keys ::
                |s.honest_nodes_states[n].bn.attestations_submitted| == 0    
        )
    }

    predicate is_sequence_attestation_duties_to_be_served_orderd(s: DVState)
    {
        && (forall i, j | 
                    && 0 <= i < j
                    && s.sequence_attestation_duties_to_be_served[i].node == s.sequence_attestation_duties_to_be_served[j].node 
                ::
                    s.sequence_attestation_duties_to_be_served[i].attestation_duty.slot <= s.sequence_attestation_duties_to_be_served[j].attestation_duty.slot
        )
        && ( forall k1: nat, k2: nat :: 
                && k1 < k2
                && s.sequence_attestation_duties_to_be_served[k1].node 
                    == s.sequence_attestation_duties_to_be_served[k2].node
                ==> 
                s.sequence_attestation_duties_to_be_served[k1].attestation_duty.slot 
                    < s.sequence_attestation_duties_to_be_served[k2].attestation_duty.slot  
           )
    }

    predicate NextPreCond(
        s: DVState
    )
    {
        forall e |  validEvent(s, e) :: NextEventPreCond(s, e)
    }
 
    predicate Next(
        s: DVState,
        s': DVState 
    )
    requires NextPreCond(s)
    {
        exists e ::
            && validEvent(s, e)
            && NextEvent(s, e, s')
    }

    predicate unchanged_fixed_paras(dv: DVState, dv': DVState)
    {
        && dv.all_nodes == dv'.all_nodes
        && dv.adversary == dv'.adversary
        && dv.honest_nodes_states.Keys == dv'.honest_nodes_states.Keys        
        && dv.dv_pubkey == dv'.dv_pubkey
        && dv.construct_signed_attestation_signature
                == dv'.construct_signed_attestation_signature
        && dv.sequence_attestation_duties_to_be_served
                == dv'.sequence_attestation_duties_to_be_served
        && ( forall n | n in dv'.honest_nodes_states.Keys :: 
                var nodes' := dv'.honest_nodes_states[n];
                && nodes'.construct_signed_attestation_signature == dv'.construct_signed_attestation_signature
                && nodes'.dv_pubkey == dv.dv_pubkey       
                && nodes'.peers == dv.all_nodes
           )
    }

    predicate blockIsValid(
        dv: DVState,
        process: DVCState,
        block: BeaconBlock
    )
    {
        var new_p := add_block_to_bn(process, block);
        blockIsValidAfterAdd(dv, new_p, block)
    }

    predicate is_valid_attestation(
        a: Attestation,
        pubkey: BLSPubkey
    )
    {
        && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(a.data.target.epoch));
        && var attestation_signing_root := compute_attestation_signing_root(a.data, fork_version);      
        verify_bls_siganture(attestation_signing_root, a.signature, pubkey)  
    }    

      // TODO: Modify isMyAttestation to include the entirety the forall premise 
    predicate pred_axiom_is_my_attestation_2(
        dv: DVState,
        new_p: DVCState,
        block: BeaconBlock
    )
    requires block.body.state_root in new_p.bn.state_roots_of_imported_blocks
    {
        var valIndex := bn_get_validator_index(new_p.bn, block.body.state_root, new_p.dv_pubkey);
        forall a | 
            && a in block.body.attestations 
            && DVC_Spec_NonInstr.isMyAttestation(
            a,
            new_p.bn,
            block,
            valIndex
            )
        ::
        exists a' ::
            && a' in dv.all_attestations_created
            && a'.data == a.data 
            && is_valid_attestation(a', dv.dv_pubkey)    
    }  

    predicate blockIsValidAfterAdd(
        dv: DVState,
        process: DVCState,
        block: BeaconBlock
    )
    requires block.body.state_root in process.bn.state_roots_of_imported_blocks
    {
        var valIndex := bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);
        && (forall a1, a2 | 
                && a1 in block.body.attestations
                && DVC_Spec_NonInstr.isMyAttestation(a1, process.bn, block, valIndex)
                && a2 in block.body.attestations
                && DVC_Spec_NonInstr.isMyAttestation(a2, process.bn, block, valIndex)                        
            ::
                a1.data.slot == a2.data.slot ==> a1 == a2  
        )      
        && pred_axiom_is_my_attestation_2(dv, process, block)
    }        


    predicate validNodeEvent(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Types.Event
    )
    requires node in s.honest_nodes_states.Keys
    requires nodeEvent.ImportedNewBlock? ==> nodeEvent.block.body.state_root in s.honest_nodes_states[node].bn.state_roots_of_imported_blocks
    {
            && (nodeEvent.ServeAttstationDuty? ==>
                    var attestation_duty_to_be_served := s.sequence_attestation_duties_to_be_served[s.index_next_attestation_duty_to_be_served];
                    && node == attestation_duty_to_be_served.node 
                    && nodeEvent.attestation_duty == attestation_duty_to_be_served.attestation_duty
            )
            && (nodeEvent.ImportedNewBlock? ==>
                    blockIsValidAfterAdd(s, s.honest_nodes_states[node], nodeEvent.block)
            )
    }

    predicate validEvent(
        s: DVState,
        event: Event
    )
    {
        event.HonestNodeTakingStep? ==>
            (
            var nodeEvent := event.event;
            && event.node in s.honest_nodes_states.Keys
            && validNodeEvent(
                add_block_to_bn_with_event(s, event.node, event.event),
                event.node,
                event.event
            )
        )  
    }    

    predicate NextEventPreCond(
        s: DVState,
        event: Event
    )
    {
        && validEvent(s, event)         
        && (event.HonestNodeTakingStep? ==> NextHonestNodePrecond(add_block_to_bn_with_event(s, event.node, event.event).honest_nodes_states[event.node], event.event))      
    }

    predicate inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue(
        dv: DVState
    )
    {
        forall n | n in dv.honest_nodes_states.Keys ::
            inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_body_body(dv.honest_nodes_states[n])
    }

    predicate inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_body_body(
        process: DVCState
    )
    {
        forall ad | ad in process.attestation_duties_queue :: ad.slot !in process.attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
    }    




    predicate NextHonestNodePrecond(
        s: DVCState,
        event: Types.Event
    )
    {
            match event 
            case ServeAttstationDuty(attestation_duty) => 
                && f_serve_attestation_duty.requires(s, attestation_duty)
            case AttConsensusDecided(id, decided_attestation_data) => 
                && inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_body_body(s)
            case ReceivedAttestationShare(attestation_share) => 
                true
            case ImportedNewBlock(block) => 
                && inv_no_instance_has_been_started_for_duties_in_attestation_duty_queue_body_body(s)
            case ResendAttestationShares => 
                true
            case NoEvent => 
                true        
    }

    predicate NextEvent(
        s: DVState,
        event: Event,
        s': DVState
    )
    requires validEvent(s, event)
    requires NextEventPreCond(s, event)  
    {
        && unchanged_fixed_paras(s, s')
        && (
            match event
                case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) => 
                    && NextHonestNode(s, node, nodeEvent, nodeOutputs, s')
                case AdeversaryTakingStep(node, new_attestation_share_sent, messagesReceivedByTheNode) => 
                    NextAdversary(s, node, new_attestation_share_sent, messagesReceivedByTheNode, s')
        )

    }

    function add_block_to_bn_with_event(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Types.Event
    ): DVState
    requires node in s.honest_nodes_states
    {
        if nodeEvent.ImportedNewBlock? then 
            s.(
                honest_nodes_states := s.honest_nodes_states[node := add_block_to_bn(s.honest_nodes_states[node], nodeEvent.block)]
            )
        else 
            s 
                  
    }

    function add_block_to_bn(
        s: DVCState,
        block: BeaconBlock
    ): DVCState
    { 
        s.(
            bn := s.bn.(
                state_roots_of_imported_blocks := s.bn.state_roots_of_imported_blocks + {block.body.state_root}
            )
        )
    }

    predicate NextHonestNode(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Types.Event,
        nodeOutputs: DVC_Spec.Outputs,
        s': DVState        
    ) 
    requires unchanged_fixed_paras(s, s')
    requires 
            && node in s.honest_nodes_states.Keys     
            && validNodeEvent( add_block_to_bn_with_event(s, node, nodeEvent), node, nodeEvent)    
            && NextHonestNodePrecond(add_block_to_bn_with_event(s, node, nodeEvent).honest_nodes_states[node], nodeEvent)        
    {
        && node in s.honest_nodes_states.Keys        
        && var s_w_honest_node_states_updated := add_block_to_bn_with_event(s, node, nodeEvent);
        && NextHonestAfterAddingBlockToBn(s_w_honest_node_states_updated, node, nodeEvent, nodeOutputs, s' )                
    }

    predicate NextHonestAfterAddingBlockToBn(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Types.Event,
        nodeOutputs: DVC_Spec.Outputs,
        s': DVState
    )
    requires unchanged_fixed_paras(s, s')
    requires node in s.honest_nodes_states.Keys 
    requires nodeEvent.ImportedNewBlock? ==> nodeEvent.block.body.state_root in s.honest_nodes_states[node].bn.state_roots_of_imported_blocks
    requires    && validNodeEvent(s, node, nodeEvent)
                && NextHonestNodePrecond(s.honest_nodes_states[node], nodeEvent)      
    {
        && var new_node_state := s'.honest_nodes_states[node];
        && s'.all_attestations_created == s.all_attestations_created + nodeOutputs.attestations_submitted
        && (
            if nodeEvent.ServeAttstationDuty? then
                var attestation_duty_to_be_served := s.sequence_attestation_duties_to_be_served[s.index_next_attestation_duty_to_be_served];
                && node == attestation_duty_to_be_served.node 
                && nodeEvent.attestation_duty == attestation_duty_to_be_served.attestation_duty
                && s'.index_next_attestation_duty_to_be_served == s.index_next_attestation_duty_to_be_served + 1
            else 
                s'.index_next_attestation_duty_to_be_served == s.index_next_attestation_duty_to_be_served
        )
        && DVC_Spec.Next(s.honest_nodes_states[node], nodeEvent, new_node_state, nodeOutputs)
        && s'.honest_nodes_states == s.honest_nodes_states[
            node := new_node_state
        ]        
        && var messagesReceivedByTheNode :=
            match nodeEvent
                case ReceivedAttestationShare(attestation_share) => {attestation_share}
                case _ => {}
            ;
        && NetworkSpec.Next(s.att_network, s'.att_network, node, nodeOutputs.att_shares_sent, messagesReceivedByTheNode)
        && (
            forall cid | cid in s.consensus_on_attestation_data.Keys ::
                var output := 
                    if nodeEvent.AttConsensusDecided? && nodeEvent.id == cid then 
                        Some(Decided(node, nodeEvent.decided_attestation_data))
                    else
                        None
                    ;

                && var validityPredicates := 
                    map n |
                            && n in s.honest_nodes_states.Keys 
                            && cid in s.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances.Keys
                        ::
                            s.honest_nodes_states[n].attestation_consensus_engine_state.active_attestation_consensus_instances[cid].validityPredicate
                    ;

                ConsensusSpec.Next(
                    s.consensus_on_attestation_data[cid],
                    validityPredicates,
                    s'.consensus_on_attestation_data[cid],
                    output
                )
        )      
        && s'.adversary == s.adversary
    }    

    

    predicate NextAdversary(
        s: DVState,
        node: BLSPubkey,
        new_attestation_shares_sent: set<MessaageWithRecipient<AttestationShare>>,
        messagesReceivedByTheNode: set<AttestationShare>,
        s': DVState
    )
    {
        && (
            && node in (s.all_nodes - s.honest_nodes_states.Keys)
            && (
                forall new_attestation_share_sent, signer | new_attestation_share_sent in new_attestation_shares_sent ::
                    var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(new_attestation_share_sent.message.data.target.epoch));
                    var attestation_signing_root := compute_attestation_signing_root(new_attestation_share_sent.message.data, fork_version);
                    verify_bls_siganture(attestation_signing_root, new_attestation_share_sent.message.signature, signer) ==> signer in s.adversary.nodes
            )
            && NetworkSpec.Next(s.att_network, s'.att_network, node, new_attestation_shares_sent, messagesReceivedByTheNode)
            && s.all_attestations_created <= s'.all_attestations_created
            && var new_aggregated_attestations_sent := s'.all_attestations_created - s.all_attestations_created;
            && (forall aggregated_attestation_sent | aggregated_attestation_sent in new_aggregated_attestations_sent ::
                    exists attestation_shares ::
                            && attestation_shares <= s'.att_network.allMessagesSent
                            && var constructed_sig := s.construct_signed_attestation_signature(attestation_shares);
                            && constructed_sig.isPresent()
                            && constructed_sig.safe_get() == aggregated_attestation_sent.signature
            )
            && s' == s.(
                att_network := s'.att_network,
                all_attestations_created := s'.all_attestations_created
            )            
           )         
    }


}