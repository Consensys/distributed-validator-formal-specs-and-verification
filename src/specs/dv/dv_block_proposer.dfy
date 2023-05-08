include "../../common/commons.dfy"
include "../../proofs/no_slashable_blocks/common/dvc_block_proposer_instrumented.dfy"
include "../consensus/consensus.dfy"
include "../network/network.dfy"
include "../../proofs/bn_axioms.dfy"
include "../../proofs/rs_axioms.dfy"


module DV_Block_Proposer_Spec 
{
    import opened Types
    import opened CommonFunctions
    
    import opened NetworkSpec
    import opened ConsensusSpec
    import opened DVC_Block_Proposer_Spec_Instr
    import opened Block_Consensus_Engine_Instr
    import opened Block_BN_Axioms
    import opened RS_Axioms
    

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
        consensus_instances_on_beacon_block: imaptotal<Slot, ConsensusInstance<BeaconBlock>>,
        randao_share_network: NetworkSpec.Network<RandaoShare>,
        block_share_network: NetworkSpec.Network<SignedBeaconBlock>,
        all_blocks_created: set<SignedBeaconBlock>,
        construct_complete_signed_randao_reveal: (set<BLSSignature>) -> Optional<BLSSignature>,
        construct_complete_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>,
        sequence_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>,
        index_next_proposer_duty_to_be_served: nat
    )

    datatype BlockEvent = 
        | AdversaryTakingStep(
                node: BLSPubkey, 
                new_sent_randao_shares: set<MessaageWithRecipient<RandaoShare>>,
                new_sent_block_shares: set<MessaageWithRecipient<SignedBeaconBlock>>,
                randaoShareReceivedByTheNode: set<RandaoShare>,
                blockShareReceivedByTheNode: set<SignedBeaconBlock>
            )
        | HonestNodeTakingStep(
                node: BLSPubkey, 
                event: Types.BlockEvent, 
                nodeOutputs: DVC_Block_Proposer_Spec_Instr.Outputs
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
                        && verify_bls_signature(signing_root, share.signature, signer)
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
                    set randao_share | randao_share in randao_shares :: randao_share.signature
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
                    set randao_share | randao_share in randao_shares :: randao_share.signature
                ;
             && construct_complete_signed_randao_reveal(randao_reveal_signature_shares).isPresent()
    {
        && randao_shares_for_the_same_proposer_duty(randao_shares, proposer_duty)
        && var signing_root := compute_randao_reveal_signing_root(proposer_duty.slot);
        && randao_share_signer_threshold(all_nodes, randao_shares, signing_root)         
        && var  randao_reveal_signature_shares :=
                    set randao_share | randao_share in randao_shares :: randao_share.signature
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
                    set randao_share | randao_share in randao_shares :: randao_share.signature
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
                && share.block == beacon_block
    }

    predicate signed_beacon_block_signer_threshold(
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
            && signed_beacon_block_signer_threshold(all_nodes, signed_beacon_blocks, signing_root) 
            ::
            && construct_complete_signed_block(signed_beacon_blocks).isPresent()
            && var complete_signed_beacon_block := construct_complete_signed_block(signed_beacon_blocks).safe_get();
            && beacon_block == complete_signed_beacon_block.block
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
        complete_block: SignedBeaconBlock
    )       
    requires && construct_complete_signed_block(signed_beacon_blocks).isPresent()
             && construct_complete_signed_block(signed_beacon_blocks).safe_get() == complete_block
    {
        && signed_beacon_blocks_for_the_same_beacon_block(signed_beacon_blocks, complete_block.block)
        && var signing_root := compute_block_signing_root(complete_block.block);
        && signed_beacon_block_signer_threshold(all_nodes, signed_beacon_blocks, signing_root)         
        && verify_bls_signature(
                    signing_root,
                    complete_block.signature,
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
            &&  construct_complete_signed_block(signed_beacon_blocks).isPresent()
            ::
            &&  var complete_block: SignedBeaconBlock := construct_complete_signed_block(signed_beacon_blocks).safe_get();
            &&  construct_complete_signed_block_assumptions_reverse_helper(
                    construct_complete_signed_block,
                    dv_pubkey,
                    all_nodes,
                    signed_beacon_blocks,
                    complete_block                
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

    predicate is_empty_bn(bn: BNState)
    {
        && bn.submitted_blocks == []
        && bn.state_roots_of_imported_blocks == {}
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
        && s.all_blocks_created == {}
        && ( forall pubkey | pubkey in s.honest_nodes_states.Keys 
                ::
                && is_empty_bn(s.honest_nodes_states[pubkey].bn)
                && DVC_Block_Proposer_Spec_Instr.Init(
                        s.honest_nodes_states[pubkey], 
                        s.dv_pubkey, 
                        s.all_nodes, 
                        s.construct_complete_signed_randao_reveal, 
                        s.construct_complete_signed_block, 
                        initial_block_slashing_db, 
                        pubkey
                    )
            )    
        &&  NetworkSpec.Init(s.block_share_network, s.all_nodes)
        &&  ( forall bci | bci in  s.consensus_instances_on_beacon_block.Values ::
                ConsensusSpec.Init(
                    bci, 
                    s.all_nodes, 
                    s.honest_nodes_states.Keys
            ))
        && ( forall i: Slot :: 
                i in s.consensus_instances_on_beacon_block.Keys
                ==> 
                !s.consensus_instances_on_beacon_block[i].decided_value.isPresent()
            )        
        && assumption_on_sequence_of_proposer_duties(s)
        && s.index_next_proposer_duty_to_be_served == 0   
        // //
        && ( forall n | n in s.honest_nodes_states.Keys ::
                |s.honest_nodes_states[n].bn.submitted_blocks| == 0    
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

    predicate is_verified_attestation_with_pubkey(
        a: Attestation,
        pubkey: BLSPubkey
    )
    {
        && var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(a.data.target.epoch));
        && var attestation_signing_root := compute_attestation_signing_root(a.data, fork_version);      
        && verify_bls_signature(attestation_signing_root, a.signature, pubkey)  
    }    

    predicate is_verified_block_with_pubkey(
        signed_block: SignedBeaconBlock,
        pubkey: BLSPubkey
    )
    {
        && var block_signing_root := compute_block_signing_root(signed_block.block);
        && verify_bls_signature(block_signing_root, signed_block.signature, pubkey)  
    }    

    predicate valid_attestations_in_beacon_block(
        dv: DVState,
        new_p: DVCState,
        block: BeaconBlock
    )
    requires block.body.state_root in new_p.bn.state_roots_of_imported_blocks
    {
        var valIndex := bn_get_validator_index(new_p.bn, block.body.state_root, new_p.dv_pubkey);
        forall a |  && a in block.body.attestations 
                    && DVC_Block_Proposer_Spec_NonInstr.isMyAttestation(
                        a,
                        new_p.bn,
                        block,
                        valIndex
                    )
        ::
        ( exists a' :: is_verified_attestation_with_pubkey(a', dv.dv_pubkey) )
    }  

    predicate is_block_of_submitted_signed_beacon_block(
        dv: DVState,
        block: BeaconBlock
    )
    {
        exists complete_signed_block: SignedBeaconBlock ::
            && complete_signed_block in dv.all_blocks_created
            && block == complete_signed_block.block
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
        && valid_attestations_in_beacon_block(dv, process, block)
        && is_block_of_submitted_signed_beacon_block(dv, block)
    } 

    predicate validNodeEvent(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Types.BlockEvent
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
        nodeEvent: Types.BlockEvent
    ): DVState
    requires node in s.honest_nodes_states.Keys
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
        event: BlockEvent
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
        dvc: DVCState,
        event: Types.BlockEvent
    )
    {
            match event 
            case ServeProposerDuty(proposer_duty) => 
                && f_serve_proposer_duty.requires(dvc, proposer_duty)
            case BlockConsensusDecided(id, decided_beacon_block) => 
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
        dv: DVState,
        event: BlockEvent
    )
    {
        && validEvent(dv, event)         
        && (event.HonestNodeTakingStep? 
            ==> 
            NextHonestNodePrecond(
                add_block_to_bn_with_event(
                    dv, 
                    event.node, 
                    event.event).honest_nodes_states[event.node], 
                event.event
            ))      
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
        event: BlockEvent,
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
                case AdversaryTakingStep(node, new_randao_share_sent, new_block_share_sent, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) => 
                        NextAdversary(s, node, new_randao_share_sent, new_block_share_sent, randaoShareReceivedByTheNode, blockShareReceivedByTheNode, s')                        
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
                && var nodes' := dv'.honest_nodes_states[n];
                && nodes'.construct_complete_signed_block == dv'.construct_complete_signed_block
                && nodes'.construct_complete_signed_randao_reveal == dv'.construct_complete_signed_randao_reveal
                && nodes'.dv_pubkey == dv.dv_pubkey       
                && nodes'.peers == dv.all_nodes
           )
    }

    predicate NextHonestNode(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Types.BlockEvent,
        nodeOutputs: DVC_Block_Proposer_Spec_Instr.Outputs,
        s': DVState        
    ) 
    requires unchanged_fixed_paras(s, s')
    requires && node in s.honest_nodes_states.Keys     
             && validNodeEvent( add_block_to_bn_with_event(s, node, nodeEvent), node, nodeEvent)    
             && NextHonestNodePrecond(add_block_to_bn_with_event(s, node, nodeEvent).honest_nodes_states[node], nodeEvent)        
    {
        && node in s.honest_nodes_states.Keys
        && var s_w_honest_node_states_updated := add_block_to_bn_with_event(s, node, nodeEvent);
        && NextHonestAfterAddingBlockToBn(s_w_honest_node_states_updated, node, nodeEvent, nodeOutputs, s' )
    }

    predicate ConsensusInstanceStep(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Types.BlockEvent,
        nodeOutputs: DVC_Block_Proposer_Spec_Instr.Outputs,
        s': DVState
    )
    {
        forall cid | cid in s.consensus_instances_on_beacon_block.Keys ::
            && var  output := 
                    if nodeEvent.BlockConsensusDecided? && nodeEvent.id == cid then 
                        Some(Decided(node, nodeEvent.decided_beacon_block))
                    else
                        None
                    ;
            && var  validityPredicates := 
                    map n |
                            && n in s.honest_nodes_states.Keys 
                            && cid in s.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks.Keys
                        ::
                            s.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances_on_beacon_blocks[cid].validityPredicate
                    ;
            &&  ConsensusSpec.Next(
                    s.consensus_instances_on_beacon_block[cid],
                    validityPredicates,
                    s'.consensus_instances_on_beacon_block[cid],
                    output
                )
    }

    predicate NextHonestAfterAddingBlockToBn(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Types.BlockEvent,
        nodeOutputs: DVC_Block_Proposer_Spec_Instr.Outputs,
        s': DVState
    )
    requires unchanged_fixed_paras(s, s')
    requires node in s.honest_nodes_states.Keys 
    requires nodeEvent.ImportedNewBlock? ==> nodeEvent.block.body.state_root in s.honest_nodes_states[node].bn.state_roots_of_imported_blocks
    requires && validNodeEvent(s, node, nodeEvent)
             && NextHonestNodePrecond(s.honest_nodes_states[node], nodeEvent)      
    {
        && var new_node_state := s'.honest_nodes_states[node];
        && s'.all_blocks_created == s.all_blocks_created + nodeOutputs.submitted_blocks
        && (
            if nodeEvent.ServeProposerDuty? then
                var proposer_duty_to_be_served := s.sequence_proposer_duties_to_be_served[s.index_next_proposer_duty_to_be_served];
                && node == proposer_duty_to_be_served.node 
                && nodeEvent.proposer_duty == proposer_duty_to_be_served.proposer_duty
                && s'.index_next_proposer_duty_to_be_served == s.index_next_proposer_duty_to_be_served + 1
            else 
                s'.index_next_proposer_duty_to_be_served == s.index_next_proposer_duty_to_be_served
        )
        && DVC_Block_Proposer_Spec_Instr.Next(s.honest_nodes_states[node], nodeEvent, new_node_state, nodeOutputs)
        && s'.honest_nodes_states == s.honest_nodes_states[
            node := new_node_state
        ]
        && s'.honest_nodes_states.Keys == s.honest_nodes_states.Keys
        && var randaoShareReceivedByTheNode :=
            match nodeEvent
                case ReceiveRandaoShare(randao_share) => {randao_share}
                case _ => {}
            ;
        && var blockShareReceivedByTheNode :=
            match nodeEvent
                case ReceiveSignedBeaconBlock(block_share) => {block_share}
                case _ => {}
            ;
        && NetworkSpec.Next(s.randao_share_network, s'.randao_share_network, node, nodeOutputs.sent_randao_shares, randaoShareReceivedByTheNode)
        && NetworkSpec.Next(s.block_share_network, s'.block_share_network, node, nodeOutputs.sent_block_shares, blockShareReceivedByTheNode)
        && ConsensusInstanceStep(s, node, nodeEvent, nodeOutputs, s')      
        && s'.adversary == s.adversary
        && s'.dv_pubkey == s.dv_pubkey      
        && s'.construct_complete_signed_randao_reveal == s.construct_complete_signed_randao_reveal
        && s'.construct_complete_signed_block == s.construct_complete_signed_block
        && node in s.honest_nodes_states.Keys 
        && var new_node_state := s'.honest_nodes_states[node];
        && DVC_Block_Proposer_Spec_Instr.Next(s.honest_nodes_states[node], nodeEvent, new_node_state, nodeOutputs)        
        && s'.honest_nodes_states == s.honest_nodes_states[node := new_node_state]
    }

    predicate NextAdversary(
        s: DVState,
        node: BLSPubkey,
        new_sent_randao_shares: set<MessaageWithRecipient<RandaoShare>>,
        new_sent_block_shares: set<MessaageWithRecipient<SignedBeaconBlock>>,
        randaoShareReceivedByTheNode: set<RandaoShare>,
        blockShareReceivedByTheNode: set<SignedBeaconBlock>,
        s': DVState
    )
    {
        && node in (s.all_nodes - s.honest_nodes_states.Keys)
        && (
            forall new_sent_randao_share, signer | new_sent_randao_share in new_sent_randao_shares ::
                var randao_reveal_signing_root := compute_randao_reveal_signing_root(new_sent_randao_share.message.slot);
                verify_bls_signature(randao_reveal_signing_root, new_sent_randao_share.message.signature, signer) ==> signer in s.adversary.nodes
        )
        && (
            forall new_sent_block_share, signer | new_sent_block_share in new_sent_block_shares ::
                var fork_version := bn_get_fork_version(new_sent_block_share.message.block.slot);
                var block_signing_root := compute_block_signing_root(new_sent_block_share.message.block);
                verify_bls_signature(block_signing_root, new_sent_block_share.message.signature, signer) ==> signer in s.adversary.nodes
        )
        && NetworkSpec.Next(s.randao_share_network, s'.randao_share_network, node, new_sent_randao_shares, randaoShareReceivedByTheNode)
        && NetworkSpec.Next(s.block_share_network, s'.block_share_network, node, new_sent_block_shares, blockShareReceivedByTheNode)        
        && s.all_blocks_created <= s'.all_blocks_created
        && var new_blocks_created := s'.all_blocks_created - s.all_blocks_created;
        && (forall new_signed_block_created | new_signed_block_created in new_blocks_created ::
                exists block_shares ::
                        && block_shares <= s'.block_share_network.allMessagesSent
                        && s.construct_complete_signed_block(block_shares).isPresent()
                        && new_signed_block_created == s.construct_complete_signed_block(block_shares).safe_get()
                        && signed_beacon_blocks_for_the_same_beacon_block(block_shares, new_signed_block_created.block)
        )
        &&  s' == 
            s.( randao_share_network := s'.randao_share_network,
                block_share_network := s'.block_share_network,
                all_blocks_created := s'.all_blocks_created
            )
    }

    predicate is_valid_signed_beacon_block(
        signed_block: SignedBeaconBlock,
        pubkey: BLSPubkey
    )
    {        
        && var block_signing_root := compute_block_signing_root(signed_block.block);      
        && verify_bls_signature(block_signing_root, signed_block.signature, pubkey)  
    }  
}