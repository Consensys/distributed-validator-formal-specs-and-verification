include "../../common/block_proposer/block_common_functions.dfy"
include "../../common/block_proposer/block_signing_functions.dfy"
include "../../common/block_proposer/block_types.dfy"
include "../dvc/dvc_block_proposer.dfy"
include "../consensus/block_consensus.dfy"
include "../network/block_network.dfy"
include "../../proofs/no_slashable_blocks/common/block_dvc_spec_axioms.dfy"


module DV_Block_Proposer_Spec 
{
    import opened Block_Types
    import opened Block_Common_Functions
    import opened Block_Signing_Functions
    import opened Block_Network_Spec
    import opened Block_Consensus_Spec
    import opened DVC_Block_Proposer_Spec_NonInstr
    import opened DVC_Block_Proposer_Spec_Axioms
    

    datatype Adversary = Adversary(
        nodes: set<BLSPubkey>
    )

    datatype ProposerDutyAndNode = ProposerDutyAndNode(
        proposer_duty: ProposerDuty,
        node: BLSPubkey
    )

    datatype DVState = DVState(
        all_nodes: set<BLSPubkey>,
        honest_nodes_states: map<BLSPubkey, DVCState>,
        adversary: Adversary,
        dv_pubkey: BLSPubkey,
        consensus_instances_on_beacon_block: imaptotal<Slot, BlockConsensusInstance<BeaconBlock>>,
        randao_share_network: Block_Network_Spec.Network<RandaoShare>,
        block_share_network: Block_Network_Spec.Network<SignedBeaconBlock>,
        all_block_created: set<SignedBeaconBlock>,
        construct_complete_signed_randao_reveal: (set<BLSSignature>) -> Optional<BLSSignature>,
        construct_complete_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>,
        
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        index_next_proposer_duty_to_be_served: nat
        
    )
    
    datatype Event = 
        | AdversaryTakingStep(
                node: BLSPubkey, 
                new_sent_randao_shares: set<MessaageWithRecipient<RandaoShare>>,
                new_block_shares_sent: set<MessaageWithRecipient<SignedBeaconBlock>>
            )
        | HonestNodeTakingStep(
                node: BLSPubkey, 
                event: Block_Types.Event, 
                nodeOutputs: DVC_Block_Proposer_Spec_NonInstr.Outputs
            )

    predicate is_randao_share_with_valid_root(
        share: RandaoShare
    )
    {
        && share.signing_root == compute_randao_reveal_signing_root(share.slot)
    }

    predicate randao_shares_for_the_same_proposer_duty(
        randao_shares: set<RandaoShare>,
        duty: ProposerDuty
    )
    {
        forall share | share in randao_shares ::
                && share.proposer_duty == duty
                && share.slot == duty.slot
                && is_randao_share_with_valid_root(share)
    }

    predicate randao_share_signer_threshold(
        all_nodes: set<BLSPubkey>,
        randao_shares: set<RandaoShare>,
        signing_root: Root
    )
    {
        && var signers := 
                    set signer, share | 
                        && share in randao_shares
                        && signer in all_nodes
                        && verify_bls_signature(signing_root, share.signature_share, signer)
                    ::
                        signer;
        && |signers| >= quorum(|all_nodes|)
        && signers <= all_nodes
           
    }    

    predicate construct_complete_signed_randao_reveal_assumptions_forward(
        construct_complete_signed_randao_reveal: (set<BLSSignature>) -> Optional<BLSSignature>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>
    )    
    {
        forall  proposer_duty: ProposerDuty, 
                signing_root: Root, 
                randao_shares: set<RandaoShare> 
            |
            && randao_shares_for_the_same_proposer_duty(randao_shares, proposer_duty)
            && randao_share_signer_threshold(all_nodes, randao_shares, signing_root) 
            ::
            && var  randao_reveal_signature_shares :=
                    set randao_share | randao_share in randao_shares :: randao_share.signature_share
                    ;
            && construct_complete_signed_randao_reveal(randao_reveal_signature_shares).isPresent()
            && verify_bls_signature(
                    signing_root,
                    construct_complete_signed_randao_reveal(randao_reveal_signature_shares).safe_get(),
                    dv_pubkey
                )
    }

    predicate construct_complete_signed_randao_reveal_assumptions_reverse_helper(
        construct_complete_signed_randao_reveal: (set<BLSSignature>) -> Optional<BLSSignature>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>,
        randao_shares: set<RandaoShare>,
        proposer_duty: ProposerDuty
    )       
    requires && var randao_reveal_signature_shares :=
                    set randao_share | randao_share in randao_shares :: randao_share.signature_share
                ;
             && construct_complete_signed_randao_reveal(randao_reveal_signature_shares).isPresent()
    {
        && randao_shares_for_the_same_proposer_duty(randao_shares, proposer_duty)
        && var signing_root := compute_randao_reveal_signing_root(proposer_duty.slot);
        && randao_share_signer_threshold(all_nodes, randao_shares, signing_root)         
        && var  randao_reveal_signature_shares :=
                    set randao_share | randao_share in randao_shares :: randao_share.signature_share
                    ;
        && verify_bls_signature(
                signing_root,
                construct_complete_signed_randao_reveal(randao_reveal_signature_shares).safe_get(),
                dv_pubkey
            )                   
    }

    predicate construct_complete_signed_randao_reveal_assumptions_reverse(
        construct_complete_signed_randao_reveal: (set<BLSSignature>) -> Optional<BLSSignature>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>
    )    
    {
        forall randao_shares: set<RandaoShare> |
            && var  randao_reveal_signature_shares :=
                    set randao_share | randao_share in randao_shares :: randao_share.signature_share
                    ;
            && construct_complete_signed_randao_reveal(randao_reveal_signature_shares).isPresent()
            ::
            exists proposer_duty: ProposerDuty
                ::      
                construct_complete_signed_randao_reveal_assumptions_reverse_helper(
                    construct_complete_signed_randao_reveal,
                    dv_pubkey,
                    all_nodes,
                    randao_shares,
                    proposer_duty                
                )
    }    

    predicate construct_complete_signed_randao_reveal_assumptions_helper(
        construct_complete_signed_randao_reveal: (set<BLSSignature>) -> Optional<BLSSignature>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>
    )
    {
        &&  construct_complete_signed_randao_reveal_assumptions_forward(
                construct_complete_signed_randao_reveal,
                dv_pubkey,
                all_nodes
            )        
        &&  construct_complete_signed_randao_reveal_assumptions_reverse(
                construct_complete_signed_randao_reveal,
                dv_pubkey,
                all_nodes
            
            )
    }

    predicate construct_complete_signed_randao_reveal_assumptions(
        s: DVState
    )
    {
        construct_complete_signed_randao_reveal_assumptions_helper(
            s.construct_complete_signed_randao_reveal,
            s.dv_pubkey,
            s.all_nodes
        ) 
    }

    predicate signed_beacon_blocks_for_the_same_beacon_block(
        signed_beacon_blocks: set<SignedBeaconBlock>,
        beacon_block: BeaconBlock
    )
    {
        forall share | share in signed_beacon_blocks ::
                && share.message == beacon_block
    }

    predicate signed_beacon_blocksigner_threshold(
        all_nodes: set<BLSPubkey>,
        signed_beacon_blocks: set<SignedBeaconBlock>,
        signing_root: Root
    )
    {
        && var signers := 
                    set signer, share | 
                        && share in signed_beacon_blocks
                        && signer in all_nodes
                        && verify_bls_signature(signing_root, share.signature, signer)
                    ::
                        signer;
        && |signers| >= quorum(|all_nodes|)
        && signers <= all_nodes
           
    }    

    predicate construct_complete_signed_block_assumptions_forward(
        construct_complete_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>
    )    
    {
        forall  beacon_block: BeaconBlock, 
                signing_root: Root, 
                signed_beacon_blocks: set<SignedBeaconBlock> 
            |
            && signed_beacon_blocks_for_the_same_beacon_block(signed_beacon_blocks, beacon_block)
            && signed_beacon_blocksigner_threshold(all_nodes, signed_beacon_blocks, signing_root) 
            ::
            && construct_complete_signed_block(signed_beacon_blocks).isPresent()
            && var complete_signed_beacon_block := construct_complete_signed_block(signed_beacon_blocks).safe_get();
            && verify_bls_signature(
                    signing_root,
                    complete_signed_beacon_block.signature,
                    dv_pubkey
                )
    }

    predicate construct_complete_signed_block_assumptions_reverse_helper(
        construct_complete_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>,
        signed_beacon_blocks: set<SignedBeaconBlock>,
        beacon_block: BeaconBlock
    )       
    requires construct_complete_signed_block(signed_beacon_blocks).isPresent()
    {
        && signed_beacon_blocks_for_the_same_beacon_block(signed_beacon_blocks, beacon_block)
        && var signing_root := compute_block_signing_root(beacon_block);
        && signed_beacon_blocksigner_threshold(all_nodes, signed_beacon_blocks, signing_root)         
        && var complete_signed_beacon_block := construct_complete_signed_block(signed_beacon_blocks).safe_get();
        && verify_bls_signature(
                    signing_root,
                    complete_signed_beacon_block.signature,
                    dv_pubkey
                )        
    }

    predicate construct_complete_signed_block_assumptions_reverse(
        construct_complete_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>
    )    
    {
        forall signed_beacon_blocks: set<SignedBeaconBlock> |
            && construct_complete_signed_block(signed_beacon_blocks).isPresent()
            ::
            exists beacon_block: BeaconBlock
                ::      
                construct_complete_signed_block_assumptions_reverse_helper(
                    construct_complete_signed_block,
                    dv_pubkey,
                    all_nodes,
                    signed_beacon_blocks,
                    beacon_block                
                )
    }    

    predicate construct_complete_signed_block_assumptions_helper(
        construct_complete_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>
    )
    {
        &&  construct_complete_signed_block_assumptions_forward(
                construct_complete_signed_block,
                dv_pubkey,
                all_nodes
            )        
        &&  construct_complete_signed_block_assumptions_reverse(
                construct_complete_signed_block,
                dv_pubkey,
                all_nodes
            
            )
    }

    predicate construct_complete_signed_block_assumptions(
        s: DVState
    )
    {
        construct_complete_signed_block_assumptions_helper(
            s.construct_complete_signed_block,
            s.dv_pubkey,
            s.all_nodes
        ) 
    }

    predicate Init(
        s: DVState,
        initial_block_slashing_db: set<SlashingDBBlock>
    )
    {
        && s.honest_nodes_states.Keys !! s.adversary.nodes !! {s.dv_pubkey}
        && s.all_nodes == s.honest_nodes_states.Keys + s.adversary.nodes
        && s.honest_nodes_states.Keys != {}
        && |s.adversary.nodes| <= f(|s.all_nodes|)
        && construct_complete_signed_randao_reveal_assumptions(s)
        && construct_complete_signed_block_assumptions(s)
        && s.all_block_created == {}
        && ( forall pubkey | pubkey in s.honest_nodes_states.Keys ::
                DVC_Block_Proposer_Spec_NonInstr.Init(
                    s.honest_nodes_states[pubkey], 
                    s.dv_pubkey, 
                    s.all_nodes, 
                    s.construct_complete_signed_randao_reveal, 
                    s.construct_complete_signed_block, 
                    initial_block_slashing_db, 
                    pubkey
            ))    
        &&  Block_Network_Spec.Init(s.block_share_network, s.all_nodes)
        &&  Block_Network_Spec.Init(s.randao_share_network, s.all_nodes)
        &&  ( forall bci | bci in  s.consensus_instances_on_beacon_block.Values ::
                Block_Consensus_Spec.Init(
                    bci, 
                    s.all_nodes, 
                    s.honest_nodes_states.Keys
            ))
        && assumption_on_sequence_of_proposer_duties(s)
        && s.index_next_proposer_duty_to_be_served == 0   
        // //
        && ( forall n | n in s.honest_nodes_states.Keys ::
                |s.honest_nodes_states[n].bn.blocks_submitted| == 0    
        )
    }

    // IMPORTANT
    predicate assumption_on_sequence_of_proposer_duties(s: DVState)
    {
        proposer_duties_are_ordered(s)
    }

    predicate proposer_duties_are_ordered(s: DVState)
    {
        && (forall i, j | 
                    && 0 <= i < j
                    && s.sequence_proposer_duties_to_be_served[i].node == s.sequence_proposer_duties_to_be_served[j].node 
                ::
                    s.sequence_proposer_duties_to_be_served[i].proposer_duty.slot < s.sequence_proposer_duties_to_be_served[j].proposer_duty.slot
        )        
    }

    predicate is_valid_attestation(
        a: Attestation,
        pubkey: BLSPubkey
    )
    {
        && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(a.data.target.epoch));
        && var attestation_signing_root := compute_attestation_signing_root(a.data, fork_version);      
        && verify_bls_signature(attestation_signing_root, a.signature, pubkey)  
    }    

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
            && DVC_Block_Proposer_Spec_NonInstr.isMyAttestation(
            a,
            new_p.bn,
            block,
            valIndex
            )
        ::
        exists a' ::
            is_valid_attestation(a', dv.dv_pubkey)    
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
                && DVC_Block_Proposer_Spec_NonInstr.isMyAttestation(a1, process.bn, block, valIndex)
                && a2 in block.body.attestations
                && DVC_Block_Proposer_Spec_NonInstr.isMyAttestation(a2, process.bn, block, valIndex)                        
            ::
                a1.data.slot == a2.data.slot ==> a1 == a2  
        )      
        && pred_axiom_is_my_attestation_2(dv, process, block)
    } 

    predicate validNodeEvent(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Block_Types.Event
    )
    requires node in s.honest_nodes_states.Keys
    requires nodeEvent.ImportedNewBlock? ==> nodeEvent.block.body.state_root in s.honest_nodes_states[node].bn.state_roots_of_imported_blocks
    {
            && (nodeEvent.ServeProposerDuty? ==>
                    var proposer_duty_to_be_served := s.sequence_proposer_duties_to_be_served[s.index_next_proposer_duty_to_be_served];
                    && node == proposer_duty_to_be_served.node 
                    && nodeEvent.proposer_duty == proposer_duty_to_be_served.proposer_duty
            )
            && (nodeEvent.ImportedNewBlock? ==>
                    blockIsValidAfterAdd(s, s.honest_nodes_states[node], nodeEvent.block)
            )
    }

    function f_add_block_to_bn(
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

    function add_block_to_bn_with_event(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Block_Types.Event
    ): DVState
    requires node in s.honest_nodes_states
    {
        if nodeEvent.ImportedNewBlock? then 
            s.(
                honest_nodes_states := s.honest_nodes_states[node := f_add_block_to_bn(s.honest_nodes_states[node], nodeEvent.block)]
            )
        else 
            s 
                  
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

    predicate NextHonestNodePrecond(
        s: DVCState,
        event: Block_Types.Event
    )
    {
            match event 
            case ServeProposerDuty(proposer_duty) => 
                && f_serve_proposer_duty.requires(s, proposer_duty)
            case BlockConsensusDecided(id, decided_attestation_data) => 
                true
            case ReceiveRandaoShare(randao_share) => 
                true
            case ReceiveSignedBeaconBlock(randao_share) => 
                true
            case ImportedNewBlock(block) => 
                true
            case ResendRandaoRevealSignatureShare => 
                true
            case ResendBlockShare => 
                true
            case NoEvent => 
                true                 
    }

    predicate NextEventPreCond(
        s: DVState,
        event: Event
    )
    {
        && validEvent(s, event)         
        && (event.HonestNodeTakingStep? ==> NextHonestNodePrecond(add_block_to_bn_with_event(s, event.node, event.event).honest_nodes_states[event.node], event.event))      
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
                        NextHonestNode(s, node, nodeEvent, nodeOutputs, s')
                case AdversaryTakingStep(node, new_randao_share_sent, new_block_share_sent) => 
                        NextAdversary(s, node, new_randao_share_sent, new_block_share_sent, s')                        
           )
    }

    function add_signed_block_to_bn(
        s: DVCState,
        block: SignedBeaconBlock
    ): DVCState
    {
        s.(
            bn := s.bn.(
                state_roots_of_imported_blocks := s.bn.state_roots_of_imported_blocks + {block.message.state_root}
            )
        )
    }

    predicate unchanged_fixed_paras(dv: DVState, dv': DVState)
    {
        && dv.all_nodes == dv'.all_nodes
        && dv.adversary == dv'.adversary
        && dv.honest_nodes_states.Keys == dv'.honest_nodes_states.Keys        
        && dv.dv_pubkey == dv'.dv_pubkey
        && dv.construct_complete_signed_block
                == dv'.construct_complete_signed_block
        && dv.construct_complete_signed_randao_reveal
                == dv'.construct_complete_signed_randao_reveal
        && dv.sequence_proposer_duties_to_be_served
                == dv'.sequence_proposer_duties_to_be_served
        && ( forall n | n in dv'.honest_nodes_states.Keys :: 
                var nodes' := dv'.honest_nodes_states[n];
                && nodes'.construct_complete_signed_block == dv'.construct_complete_signed_block
                && nodes'.dv_pubkey == dv.dv_pubkey       
                && nodes'.peers == dv.all_nodes
           )
    }

    predicate NextHonestNode(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Block_Types.Event,
        nodeOutputs: DVC_Block_Proposer_Spec_NonInstr.Outputs,
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

    predicate reliable_networks(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Block_Types.Event,
        nodeOutputs: DVC_Block_Proposer_Spec_NonInstr.Outputs,
        s': DVState
    )
    {
        match nodeEvent
            case ReceiveRandaoShare(randao_share) =>
                    ( && Block_Network_Spec.Next(s.randao_share_network, 
                                               s'.randao_share_network, 
                                               node, 
                                               nodeOutputs.sent_randao_shares, 
                                               {randao_share})
                      && Block_Network_Spec.Next(s.block_share_network, 
                                               s'.block_share_network, 
                                               node, 
                                               nodeOutputs.block_shares_sent, 
                                               {}))
            case ReceiveSignedBeaconBlock(block_share) =>
                    ( && Block_Network_Spec.Next(s.randao_share_network, 
                                               s'.randao_share_network, 
                                               node, 
                                               nodeOutputs.sent_randao_shares, 
                                               {})
                      && Block_Network_Spec.Next(s.block_share_network, 
                                               s'.block_share_network, 
                                               node, 
                                               nodeOutputs.block_shares_sent, 
                                               {block_share}))
            case _ =>
                    ( && Block_Network_Spec.Next(s.randao_share_network, 
                                               s'.randao_share_network, 
                                               node, 
                                               nodeOutputs.sent_randao_shares, 
                                               {})
                      && Block_Network_Spec.Next(s.block_share_network, 
                                               s'.block_share_network, 
                                               node, 
                                               nodeOutputs.block_shares_sent, 
                                               {}))
    }

    predicate is_valid_decided_consensus_instance(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Block_Types.Event,
        nodeOutputs: DVC_Block_Proposer_Spec_NonInstr.Outputs,
        s': DVState
    )
    {
        forall slot | slot in s.consensus_instances_on_beacon_block.Keys ::
                && var output := 
                        if nodeEvent.BlockConsensusDecided? && nodeEvent.block.slot == slot then 
                            Some(Decided(node, nodeEvent.block))
                        else
                            None
                    ;
                && var validityPredicates := 
                        map nid | && nid in s.honest_nodes_states.Keys 
                                  && slot in s.honest_nodes_states[nid].block_consensus_engine_state.active_consensus_instances_on_beacon_block.Keys
                                        ::
                                            s.honest_nodes_states[nid].block_consensus_engine_state.active_consensus_instances_on_beacon_block[slot].validityPredicate
                    ;
                && Block_Consensus_Spec.Next(
                        s.consensus_instances_on_beacon_block[slot],
                        validityPredicates,
                        s'.consensus_instances_on_beacon_block[slot],
                        output
                    )  
    }

    predicate NextHonestAfterAddingBlockToBn(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Block_Types.Event,
        nodeOutputs: DVC_Block_Proposer_Spec_NonInstr.Outputs,
        s': DVState
    )
    requires unchanged_fixed_paras(s, s')
    requires node in s.honest_nodes_states.Keys 
    requires nodeEvent.ImportedNewBlock? ==> nodeEvent.block.body.state_root in s.honest_nodes_states[node].bn.state_roots_of_imported_blocks
    requires    && validNodeEvent(s, node, nodeEvent)
                && NextHonestNodePrecond(s.honest_nodes_states[node], nodeEvent)      
    
    {
        && s'.honest_nodes_states.Keys == s.honest_nodes_states.Keys
        && s'.adversary == s.adversary
        && s'.dv_pubkey == s.dv_pubkey      
        && s'.construct_complete_signed_randao_reveal == s.construct_complete_signed_randao_reveal
        && s'.construct_complete_signed_block == s.construct_complete_signed_block
        && node in s.honest_nodes_states.Keys 
        && var new_node_state := s'.honest_nodes_states[node];
        && DVC_Block_Proposer_Spec_NonInstr.Next(s.honest_nodes_states[node], nodeEvent, new_node_state, nodeOutputs)        
        && s'.honest_nodes_states == s.honest_nodes_states[node := new_node_state]    
        && reliable_networks(s, node, nodeEvent, nodeOutputs, s')
        && is_valid_decided_consensus_instance(s, node, nodeEvent, nodeOutputs, s')            
    }

    predicate NextAdversary(
        s: DVState,
        node: BLSPubkey,
        new_wrapped_sent_randao_shares: set<MessaageWithRecipient<RandaoShare>>,
        new_wrapped_block_shares_sent: set<MessaageWithRecipient<SignedBeaconBlock>>,
        s': DVState
    )
    {
        && s'.honest_nodes_states.Keys == s.honest_nodes_states.Keys
        && s'.adversary == s.adversary
        && s'.dv_pubkey == s.dv_pubkey      
        && s'.construct_complete_signed_randao_reveal == s.construct_complete_signed_randao_reveal
        && s'.construct_complete_signed_block == s.construct_complete_signed_block
        && node in (s.all_nodes - s.honest_nodes_states.Keys)
        && node in s.adversary.nodes
        && ( forall msg :: msg in new_wrapped_sent_randao_shares 
                ==> verify_bls_signature(msg.message.slot, msg.message.signature_share, node)                     
           )
        && ( forall msg :: msg in new_wrapped_block_shares_sent 
                ==> verify_bls_signature(msg.message.message, msg.message.signature, node)                     
           )
        && Block_Network_Spec.Next(
                s.randao_share_network, 
                s'.randao_share_network, 
                node, 
                new_wrapped_sent_randao_shares, 
                {})
        && Block_Network_Spec.Next(
                s.block_share_network, 
                s'.block_share_network, 
                node, 
                new_wrapped_block_shares_sent, 
                {})
        && s' == s.(honest_nodes_states := s'.honest_nodes_states,
                    randao_share_network := s'.randao_share_network,
                    block_share_network := s'.block_share_network,
                    consensus_instances_on_beacon_block := s'.consensus_instances_on_beacon_block
                   )        
    }
}