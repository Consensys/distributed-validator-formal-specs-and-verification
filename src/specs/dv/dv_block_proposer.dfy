include "../../common/commons.dfy"
include "../../proofs/no_slashable_blocks/common/dvc_block_proposer_instrumented.dfy"
include "../consensus/consensus.dfy"
include "../dvc/consensus_engine.dfy"
include "../network/network.dfy"
include "../../proofs/bn_axioms.dfy"
include "../../proofs/rs_axioms.dfy"


module Block_DV 
{
    import opened Types
    import opened Common_Functions
    import opened Signing_Methods
    import opened Network_Spec
    import opened Consensus
    import opened Consensus_Engine
    import opened Block_DVC
    import opened BN_Axioms
    import opened RS_Axioms
    import opened DV_Block_Proposer_Assumptions
    
    predicate dvcs_are_initialized_with_empty_beacon_nodes(
        s: BlockDVState,
        initial_block_slashing_db: set<SlashingDBBlock>
    )
    {
        forall pubkey | pubkey in s.honest_nodes_states.Keys 
                ::
                && s.honest_nodes_states[pubkey].bn.submitted_data == []
                && s.honest_nodes_states[pubkey].bn.state_roots_of_imported_blocks == {}
                && Block_DVC.init(
                        s.honest_nodes_states[pubkey], 
                        s.dv_pubkey, 
                        s.all_nodes, 
                        s.construct_complete_signed_randao_reveal, 
                        s.construct_complete_signed_block, 
                        initial_block_slashing_db, 
                        pubkey
                    )        
    }

    predicate consensus_instances_are_initialized_with_no_decision_values(
        s: BlockDVState
    )
    {
        &&  ( forall ci | ci in  s.consensus_instances_on_beacon_block.Values ::
                Consensus.init(ci, s.all_nodes, s.honest_nodes_states.Keys)
            )
        && ( forall i: Slot :: i in s.consensus_instances_on_beacon_block 
                            ==> !s.consensus_instances_on_beacon_block[i].decided_value.isPresent()
            )       
    }

    predicate init(
        s: BlockDVState,
        initial_block_slashing_db: set<SlashingDBBlock>
    )
    {
        && assump_set_of_byz_nodes(s.dv_pubkey, s.all_nodes, s.honest_nodes_states.Keys, s.adversary.nodes)
        && assump_construction_of_complete_signed_randao_reveal(
                s.construct_complete_signed_randao_reveal,
                s.dv_pubkey,
                s.all_nodes
            )
        && assump_construction_of_complete_signed_block(
                s.construct_complete_signed_block,
                s.dv_pubkey,
                s.all_nodes
            )
        && s.all_blocks_created == {}
        && dvcs_are_initialized_with_empty_beacon_nodes(s, initial_block_slashing_db)
        && Network_Spec.init(s.block_share_network, s.all_nodes)
        && consensus_instances_are_initialized_with_no_decision_values(s)      
        && assump_seq_of_proposer_duties(s.sequence_of_proposer_duties_to_be_served)
        && s.index_next_proposer_duty_to_be_served == 0   
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

    predicate block_signature_is_signed_with_pubkey(
        signed_block: SignedBeaconBlock,
        pubkey: BLSPubkey
    )
    {
        && var block_signing_root := compute_block_signing_root(signed_block.block);
        && verify_bls_signature(block_signing_root, signed_block.signature, pubkey)  
    }    

    predicate all_attestations_in_beacon_block_are_valid(
        dv: BlockDVState,
        new_p: BlockDVCState,
        block: BeaconBlock
    )
    requires block.body.state_root in new_p.bn.state_roots_of_imported_blocks
    {
        var valIndex := af_bn_get_validator_index(new_p.bn, block.body.state_root, new_p.dv_pubkey);
        forall a |  && a in block.body.attestations 
                    && Non_Instr_Block_DVC.has_correct_validator_index(
                        a,
                        new_p.bn,
                        block,
                        valIndex
                    )
        ::
        ( exists a' :: att_signature_is_signed_with_pubkey(a', dv.dv_pubkey) )
    }  

    predicate exists_submitted_signed_beacon_block_for_given_block(
        dv: BlockDVState,
        block: BeaconBlock
    )
    {
        exists complete_signed_block: SignedBeaconBlock ::
            && complete_signed_block in dv.all_blocks_created
            && block == complete_signed_block.block
    }
    

    predicate valid_Block(
        dv: BlockDVState,
        process: BlockDVCState,
        block: BeaconBlock
    )
    requires block.body.state_root in process.bn.state_roots_of_imported_blocks
    {
        var valIndex := af_bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);
        && (forall a1, a2 | 
                && a1 in block.body.attestations
                && Non_Instr_Block_DVC.has_correct_validator_index(a1, process.bn, block, valIndex)
                && a2 in block.body.attestations
                && Non_Instr_Block_DVC.has_correct_validator_index(a2, process.bn, block, valIndex)                        
            ::
                a1.data.slot == a2.data.slot ==> a1 == a2  
        )      
        && all_attestations_in_beacon_block_are_valid(dv, process, block)
        && exists_submitted_signed_beacon_block_for_given_block(dv, block)
    } 

    predicate valid_ServeAttestationDuty_and_ImportedNewBlock_events(
        s: BlockDVState,
        node: BLSPubkey,
        nodeEvent: BlockEvent
    )
    requires node in s.honest_nodes_states.Keys
    requires nodeEvent.ImportedNewBlock? ==> nodeEvent.block.body.state_root in s.honest_nodes_states[node].bn.state_roots_of_imported_blocks
    {
            && (nodeEvent.ServeProposerDuty? ==>
                    var proposer_duty_to_be_served := s.sequence_of_proposer_duties_to_be_served[s.index_next_proposer_duty_to_be_served];
                    && node == proposer_duty_to_be_served.node 
                    && nodeEvent.proposer_duty == proposer_duty_to_be_served.proposer_duty
            )
            && (nodeEvent.ImportedNewBlock? ==>
                    valid_Block(s, s.honest_nodes_states[node], nodeEvent.block)
            )
    }

    function f_add_block_to_bn(
        s: BlockDVCState,
        block: BeaconBlock
    ): BlockDVCState
    { 
        s.(
            bn := s.bn.(
                state_roots_of_imported_blocks := s.bn.state_roots_of_imported_blocks + {block.body.state_root}
            )
        )
    }

    function f_add_block_to_bn_if_ImportedNewBlock_event(
        s: BlockDVState,
        node: BLSPubkey,
        nodeEvent: BlockEvent
    ): BlockDVState
    requires node in s.honest_nodes_states.Keys
    {
        if nodeEvent.ImportedNewBlock? then 
            s.(
                honest_nodes_states := s.honest_nodes_states[node := f_add_block_to_bn(s.honest_nodes_states[node], nodeEvent.block)]
            )
        else 
            s 
                  
    }    

    predicate valid_HonestNodeTakingStep_event(
        s: BlockDVState,
        event: DVBlockEvent
    )
    {
        event.HonestNodeTakingStep? ==>
            (
            var nodeEvent := event.event;
            && event.node in s.honest_nodes_states.Keys
            && valid_ServeAttestationDuty_and_ImportedNewBlock_events(
                f_add_block_to_bn_if_ImportedNewBlock_event(s, event.node, event.event),
                event.node,
                event.event
            )
        )  
    }  

    predicate next_honest_node_event_preconditions(
        dvc: BlockDVCState,
        event: BlockEvent
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

    predicate next_event_preconditions(
        dv: BlockDVState,
        event: DVBlockEvent
    )
    {
        && valid_HonestNodeTakingStep_event(dv, event)         
        && (event.HonestNodeTakingStep? 
            ==> 
            next_honest_node_event_preconditions(
                f_add_block_to_bn_if_ImportedNewBlock_event(
                    dv, 
                    event.node, 
                    event.event).honest_nodes_states[event.node], 
                event.event
            ))      
    }

    predicate next_preconditions(
        s: BlockDVState
    )
    {
        forall e |  valid_HonestNodeTakingStep_event(s, e) :: next_event_preconditions(s, e)
    }

    predicate next(
        s: BlockDVState,
        s': BlockDVState 
    )
    requires next_preconditions(s)
    {
        exists e :: 
            && valid_HonestNodeTakingStep_event(s, e)
            && next_event(s, e, s')
    }

    predicate next_event(
        s: BlockDVState,
        event: DVBlockEvent,
        s': BlockDVState
    )
    requires valid_HonestNodeTakingStep_event(s, event)
    requires next_event_preconditions(s, event)  
    {
        && next_unchanged(s, s')
        && (
            match event
                case HonestNodeTakingStep(node, nodeEvent, nodeOutputs) => 
                        next_honest_node(s, node, nodeEvent, nodeOutputs, s')
                case AdversaryTakingStep(node, new_randao_share_sent, new_block_share_sent, randaoShareReceivedByTheNode, blockShareReceivedByTheNode) => 
                        next_adversary(s, node, new_randao_share_sent, new_block_share_sent, randaoShareReceivedByTheNode, blockShareReceivedByTheNode, s')                        
           )
    }

    predicate next_unchanged(dv: BlockDVState, dv': BlockDVState)
    {
        && dv.all_nodes == dv'.all_nodes
        && dv.adversary == dv'.adversary
        && dv.honest_nodes_states.Keys == dv'.honest_nodes_states.Keys        
        && dv.dv_pubkey == dv'.dv_pubkey
        && dv.construct_complete_signed_block == dv'.construct_complete_signed_block
        && dv.construct_complete_signed_randao_reveal == dv'.construct_complete_signed_randao_reveal
        && dv.sequence_of_proposer_duties_to_be_served
                == dv'.sequence_of_proposer_duties_to_be_served
        && ( forall n | n in dv'.honest_nodes_states.Keys :: 
                && var nodes' := dv'.honest_nodes_states[n];
                && nodes'.construct_complete_signed_block == dv'.construct_complete_signed_block
                && nodes'.construct_complete_signed_randao_reveal == dv'.construct_complete_signed_randao_reveal
                && nodes'.dv_pubkey == dv.dv_pubkey       
                && nodes'.peers == dv.all_nodes
           )
    }

    predicate next_honest_node(
        s: BlockDVState,
        node: BLSPubkey,
        nodeEvent: BlockEvent,
        nodeOutputs: BlockOutputs,
        s': BlockDVState        
    ) 
    requires next_unchanged(s, s')
    requires && node in s.honest_nodes_states.Keys     
             && valid_ServeAttestationDuty_and_ImportedNewBlock_events( f_add_block_to_bn_if_ImportedNewBlock_event(s, node, nodeEvent), node, nodeEvent)    
             && next_honest_node_event_preconditions(f_add_block_to_bn_if_ImportedNewBlock_event(s, node, nodeEvent).honest_nodes_states[node], nodeEvent)        
    {
        && node in s.honest_nodes_states.Keys
        && var s_w_honest_node_states_updated := f_add_block_to_bn_if_ImportedNewBlock_event(s, node, nodeEvent);
        && next_honest_node_after_adding_block_to_bn(s_w_honest_node_states_updated, node, nodeEvent, nodeOutputs, s' )
    }

    predicate consensus_instance_step(
        s: BlockDVState,
        node: BLSPubkey,
        nodeEvent: BlockEvent,
        nodeOutputs: BlockOutputs,
        s': BlockDVState
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
                            && cid in s.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances.Keys
                        ::
                            s.honest_nodes_states[n].block_consensus_engine_state.active_consensus_instances[cid].validityPredicate
                    ;
            &&  Consensus.next(
                    s.consensus_instances_on_beacon_block[cid],
                    validityPredicates,
                    s'.consensus_instances_on_beacon_block[cid],
                    output
                )
    }

    predicate next_proposer_duty_and_node(
        s: BlockDVState,
        node: BLSPubkey,
        nodeEvent: BlockEvent,
        s': BlockDVState
    )
    {
        if nodeEvent.ServeProposerDuty? then
            && var proposer_duty_to_be_served := s.sequence_of_proposer_duties_to_be_served[s.index_next_proposer_duty_to_be_served];
            && node == proposer_duty_to_be_served.node 
            && nodeEvent.proposer_duty == proposer_duty_to_be_served.proposer_duty
            && s'.index_next_proposer_duty_to_be_served == s.index_next_proposer_duty_to_be_served + 1
        else 
            s'.index_next_proposer_duty_to_be_served == s.index_next_proposer_duty_to_be_served
    }

    predicate update_node_state(
        s: BlockDVState,
        node: BLSPubkey,
        new_node_state: BlockDVCState,
        s': BlockDVState
    )
    {
        s'.honest_nodes_states == s.honest_nodes_states[
                                        node := new_node_state
                                    ]
    }

    predicate update_network(
        s: BlockDVState,
        node: BLSPubkey,
        nodeEvent: BlockEvent,
        nodeOutputs: BlockOutputs,
        s': BlockDVState
    )
    {
        && var  randaoShareReceivedByTheNode :=
                match nodeEvent
                    case ReceiveRandaoShare(randao_share) => {randao_share}
                    case _ => {}
                ;
        && var  blockShareReceivedByTheNode :=
                match nodeEvent
                    case ReceiveSignedBeaconBlock(block_share) => {block_share}
                    case _ => {}
                ;
        && Network_Spec.next(s.randao_share_network, s'.randao_share_network, node, nodeOutputs.sent_randao_shares, randaoShareReceivedByTheNode)
        && Network_Spec.next(s.block_share_network, s'.block_share_network, node, nodeOutputs.sent_block_shares, blockShareReceivedByTheNode)
    }

    predicate next_honest_node_after_adding_block_to_bn(
        s: BlockDVState,
        node: BLSPubkey,
        nodeEvent: BlockEvent,
        nodeOutputs: BlockOutputs,
        s': BlockDVState
    )
    requires next_unchanged(s, s')
    requires node in s.honest_nodes_states.Keys 
    requires nodeEvent.ImportedNewBlock? ==> nodeEvent.block.body.state_root in s.honest_nodes_states[node].bn.state_roots_of_imported_blocks
    requires && valid_ServeAttestationDuty_and_ImportedNewBlock_events(s, node, nodeEvent)
             && next_honest_node_event_preconditions(s.honest_nodes_states[node], nodeEvent)      
    {
        && node in s.honest_nodes_states.Keys 
        && var new_node_state := s'.honest_nodes_states[node];
        && s'.all_blocks_created == s.all_blocks_created + nodeOutputs.submitted_data
        && next_proposer_duty_and_node(s, node, nodeEvent, s')
        && Block_DVC.next(s.honest_nodes_states[node], nodeEvent, new_node_state, nodeOutputs)
        && update_node_state(s, node, new_node_state, s')
        && s'.honest_nodes_states.Keys == s.honest_nodes_states.Keys
        && update_network(s, node, nodeEvent, nodeOutputs, s')
        && consensus_instance_step(s, node, nodeEvent, nodeOutputs, s')      
    }

    predicate next_adversary(
        s: BlockDVState,
        node: BLSPubkey,
        new_sent_randao_shares: set<MessaageWithRecipient<RandaoShare>>,
        new_sent_block_shares: set<MessaageWithRecipient<SignedBeaconBlock>>,
        randaoShareReceivedByTheNode: set<RandaoShare>,
        blockShareReceivedByTheNode: set<SignedBeaconBlock>,
        s': BlockDVState
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
                var fork_version := af_bn_get_fork_version(new_sent_block_share.message.block.slot);
                var block_signing_root := compute_block_signing_root(new_sent_block_share.message.block);
                verify_bls_signature(block_signing_root, new_sent_block_share.message.signature, signer) ==> signer in s.adversary.nodes
        )
        && Network_Spec.next(s.randao_share_network, s'.randao_share_network, node, new_sent_randao_shares, randaoShareReceivedByTheNode)
        && Network_Spec.next(s.block_share_network, s'.block_share_network, node, new_sent_block_shares, blockShareReceivedByTheNode)        
        && s.all_blocks_created <= s'.all_blocks_created
        && var new_blocks_created := s'.all_blocks_created - s.all_blocks_created;
        && (forall new_signed_block_created | new_signed_block_created in new_blocks_created ::
                exists block_shares ::
                        && block_shares <= s'.block_share_network.allMessagesSent
                        && s.construct_complete_signed_block(block_shares).isPresent()
                        && new_signed_block_created == s.construct_complete_signed_block(block_shares).safe_get()
                        && signed_beacon_blocks_for_same_beacon_block(block_shares, new_signed_block_created.block)
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

module DV_Block_Proposer_Assumptions 
{
    import opened Types
    import opened Common_Functions
    import opened Signing_Methods
    import opened Network_Spec
    import opened Consensus
    import opened Consensus_Engine
    import opened Block_DVC
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
    
    predicate is_randao_share_with_valid_root(
        share: RandaoShare
    )
    {
        && share.signing_root == compute_randao_reveal_signing_root(share.slot)
    }

    predicate randao_shares_for_same_proposer_duty(
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

    predicate assump_construction_of_complete_signed_randao_reveal_forward(
        construct_complete_signed_randao_reveal: (set<BLSSignature>) -> Optional<BLSSignature>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>
    )    
    {
        forall  proposer_duty: ProposerDuty, 
                signing_root: Root, 
                randao_shares: set<RandaoShare> 
            |
            && randao_shares_for_same_proposer_duty(randao_shares, proposer_duty)
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

    predicate assump_construction_of_complete_signed_randao_reveal_reverse_helper(
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
        && randao_shares_for_same_proposer_duty(randao_shares, proposer_duty)
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

    predicate assump_construction_of_complete_signed_randao_reveal_reverse(
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
                assump_construction_of_complete_signed_randao_reveal_reverse_helper(
                    construct_complete_signed_randao_reveal,
                    dv_pubkey,
                    all_nodes,
                    randao_shares,
                    proposer_duty                
                )
    }    

    predicate assump_construction_of_complete_signed_randao_reveal(
        construct_complete_signed_randao_reveal: (set<BLSSignature>) -> Optional<BLSSignature>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>
    )
    {
        &&  assump_construction_of_complete_signed_randao_reveal_forward(
                construct_complete_signed_randao_reveal,
                dv_pubkey,
                all_nodes
            )        
        &&  assump_construction_of_complete_signed_randao_reveal_reverse(
                construct_complete_signed_randao_reveal,
                dv_pubkey,
                all_nodes
            
            )
    }

    predicate signed_beacon_blocks_for_same_beacon_block(
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

    predicate assump_construction_of_complete_signed_block_forward(
        construct_complete_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>
    )    
    {
        forall  beacon_block: BeaconBlock, 
                signing_root: Root, 
                signed_beacon_blocks: set<SignedBeaconBlock> 
            |
            && signed_beacon_blocks_for_same_beacon_block(signed_beacon_blocks, beacon_block)
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

    predicate assump_construction_of_complete_signed_block_reverse_helper(
        construct_complete_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>,
        signed_beacon_blocks: set<SignedBeaconBlock>,
        complete_block: SignedBeaconBlock
    )       
    requires && construct_complete_signed_block(signed_beacon_blocks).isPresent()
             && construct_complete_signed_block(signed_beacon_blocks).safe_get() == complete_block
    {
        && signed_beacon_blocks_for_same_beacon_block(signed_beacon_blocks, complete_block.block)
        && var signing_root := compute_block_signing_root(complete_block.block);
        && signed_beacon_block_signer_threshold(all_nodes, signed_beacon_blocks, signing_root)         
        && verify_bls_signature(
                    signing_root,
                    complete_block.signature,
                    dv_pubkey
                )        
    }

    predicate assump_construction_of_complete_signed_block_reverse(
        construct_complete_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>
    )    
    {
        forall signed_beacon_blocks: set<SignedBeaconBlock> |
            &&  construct_complete_signed_block(signed_beacon_blocks).isPresent()
            ::
            &&  var complete_block: SignedBeaconBlock := construct_complete_signed_block(signed_beacon_blocks).safe_get();
            &&  assump_construction_of_complete_signed_block_reverse_helper(
                    construct_complete_signed_block,
                    dv_pubkey,
                    all_nodes,
                    signed_beacon_blocks,
                    complete_block                
                )
    }    

    predicate assump_construction_of_complete_signed_block(
        construct_complete_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>,
        dv_pubkey: BLSPubkey,
        all_nodes: set<BLSPubkey>
    )
    {
        &&  assump_construction_of_complete_signed_block_forward(
                construct_complete_signed_block,
                dv_pubkey,
                all_nodes
            )        
        &&  assump_construction_of_complete_signed_block_reverse(
                construct_complete_signed_block,
                dv_pubkey,
                all_nodes
            
            )
    }

    predicate assump_seq_of_proposer_duties(sequence_of_proposer_duties_to_be_served: iseq<ProposerDutyAndNode>)
    {
        && (forall i, j | 
                    && 0 <= i < j
                    && sequence_of_proposer_duties_to_be_served[i].node == sequence_of_proposer_duties_to_be_served[j].node 
                ::
                    sequence_of_proposer_duties_to_be_served[i].proposer_duty.slot < sequence_of_proposer_duties_to_be_served[j].proposer_duty.slot
        )        
    } 
}