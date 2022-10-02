include "../commons.dfy"
include "dvc_spec.dfy"
include "consensus.dfy"
include "network.dfy"
include "../att_spec_proofs/inv.dfy"


module DV 
{
    import opened Types
    import opened CommonFunctions
    import opened NetworkSpec
    import opened ConsensusSpec
    import opened DVCNode_Spec
    import opened DVCNode_Externs_Proofs
    

    datatype Adversary = Adversary(
        nodes: set<BLSPubkey>  
    )

    datatype AttestationDutyAndNode = AttestationDutyAndNode(
        attestation_duty: AttestationDuty,
        node: BLSPubkey
    )

    datatype DVState = DVState(
        all_nodes: set<BLSPubkey>,
        honest_nodes_states: map<BLSPubkey, DVCNodeState>,
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
        ghost highest_slot_with_dvn_signed_att: Optional<Slot>
    )

    datatype Event = 
    | AdeversaryTakingStep(node: BLSPubkey, new_attestation_shares_sent: set<MessaageWithRecipient<AttestationShare>>,
        messagesReceivedByTheNode: set<AttestationShare>)
    | HonestNodeTakingStep(node: BLSPubkey, event: Types.Event, nodeOutputs: DVCNode_Spec.Outputs)

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
         
        // &&
        //     (
        //     forall 
        //         att_shares: set<AttestationShare>
        //             |
        //              construct_signed_attestation_signature(att_shares).isPresent()
        //         ::
        //         exists x ::
        //         construct_signed_attestation_signature_assumptions_helper_3(
        //             construct_signed_attestation_signature,
        //             dv_pubkey,
        //             all_nodes,
        //             att_shares,
        //             construct_signed_attestation_signature(att_shares).safe_get()
        //         )

        // )   
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
                DVCNode_Spec.Init(s.honest_nodes_states[n], s.dv_pubkey, s.all_nodes, s.construct_signed_attestation_signature, initial_attestation_slashing_db, n)
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
    }

    predicate is_sequence_attestation_duties_to_be_served_orderd(s: DVState)
    {
        && (forall i, j | 
                    && 0 <= i < j
                    && s.sequence_attestation_duties_to_be_served[i].node == s.sequence_attestation_duties_to_be_served[j].node 
                ::
                    s.sequence_attestation_duties_to_be_served[i].attestation_duty.slot <= s.sequence_attestation_duties_to_be_served[j].attestation_duty.slot
        )
        // && ( forall k1: nat, k2: nat :: 
        //         s.sequence_attestation_duties_to_be_served[k1].attestation_duty.slot 
        //             == s.sequence_attestation_duties_to_be_served[k2].attestation_duty.slot  
        //         ==> 
        //         s.sequence_attestation_duties_to_be_served[k1].attestation_duty
        //             == s.sequence_attestation_duties_to_be_served[k2].attestation_duty
        //    )
        && ( forall k1: nat, k2: nat :: 
                && k1 < k2
                && s.sequence_attestation_duties_to_be_served[k1].node 
                    == s.sequence_attestation_duties_to_be_served[k2].node
                ==> 
                s.sequence_attestation_duties_to_be_served[k1].attestation_duty.slot 
                    < s.sequence_attestation_duties_to_be_served[k2].attestation_duty.slot  
           )
    }
    
    predicate Next(
        s: DVState,
        s': DVState 
    )
    {
        exists e ::
            NextEvent(s, e, s')
    }

    predicate unchanged_fixed_paras(dvn: DVState, dvn': DVState)
    {
        && dvn.all_nodes == dvn'.all_nodes
        && dvn.adversary == dvn'.adversary
        && dvn.honest_nodes_states.Keys == dvn'.honest_nodes_states.Keys        
        && dvn.dv_pubkey == dvn'.dv_pubkey
        && dvn.construct_signed_attestation_signature
                == dvn'.construct_signed_attestation_signature
        && dvn.sequence_attestation_duties_to_be_served
                == dvn'.sequence_attestation_duties_to_be_served
        && ( forall n | n in dvn'.honest_nodes_states.Keys :: 
                var nodes' := dvn'.honest_nodes_states[n];
                && nodes'.construct_signed_attestation_signature == dvn'.construct_signed_attestation_signature
                && nodes'.dv_pubkey == dvn.dv_pubkey       
                && nodes'.peers == dvn.all_nodes
           )
    }

    predicate NextEvent(
        s: DVState,
        event: Event,
        s': DVState
    )
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

    function add_block_to_bn(
        s: DVCNodeState,
        block: BeaconBlock
    ): DVCNodeState
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
        nodeOutputs: DVCNode_Spec.Outputs,
        s': DVState        
    ) 
    requires unchanged_fixed_paras(s, s')
    {
        && node in s.honest_nodes_states.Keys        
        && var s_w_honest_node_states_updated :=
            if nodeEvent.ImportedNewBlock? then 
                s.(
                    honest_nodes_states := s.honest_nodes_states[node := add_block_to_bn(s.honest_nodes_states[node], nodeEvent.block)]
                )
            else 
                s 
            ;
        && NextHonestAfterAddingBlockToBn(s_w_honest_node_states_updated, node, nodeEvent, nodeOutputs, s' )                
    }

    predicate NextHonestAfterAddingBlockToBn(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Types.Event,
        nodeOutputs: DVCNode_Spec.Outputs,
        s': DVState
    )
    requires unchanged_fixed_paras(s, s')
    {
        && node in s.honest_nodes_states.Keys 
        && var new_node_state := s'.honest_nodes_states[node];
        && DVCNode_Spec.Next(s.honest_nodes_states[node], nodeEvent, new_node_state, nodeOutputs)
        && s'.honest_nodes_states == s.honest_nodes_states[
            node := new_node_state
        ]
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
        && var messagesReceivedByTheNode :=
            match nodeEvent
                case ReceviedAttesttionShare(attestation_share) => {attestation_share}
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
                            && cid in s.honest_nodes_states[n].attestation_consensus_engine_state.attestation_consensus_active_instances.Keys
                        ::
                            s.honest_nodes_states[n].attestation_consensus_engine_state.attestation_consensus_active_instances[cid].validityPredicate
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
                            // && var sig_shares := set x | x in attestation_shares :: x.signature;
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