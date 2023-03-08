include "../../common/block_proposer/block_common_functions.dfy"
include "../../common/block_proposer/block_signing_functions.dfy"
include "../../common/block_proposer/block_types.dfy"
include "../dvc/dvc_block_proposer.dfy"
include "../consensus/block_consensus.dfy"
include "../network/block_network.dfy"

module DV_Block_Proposer_Spec 
{
    import opened Block_Types
    import opened Block_Common_Functions
    import opened Block_Signing_Functions
    import opened Block_Network_Spec
    import opened Block_Consensus_Spec
    import opened DVC_Block_Proposer_Spec_NonInstr
    

    datatype Adversary = Adversary(
        nodes: set<BLSPubkey>
    )

    datatype DVState = DVState(
        all_nodes: set<BLSPubkey>,
        honest_nodes_states: map<BLSPubkey, DVCState>,
        adversary: Adversary,
        dv_pubkey: BLSPubkey,
        block_consensus_instances: imaptotal<Slot, BlockConsensusInstance<BeaconBlock>>,
        randao_share_network: Block_Network_Spec.Network<RandaoShare>,
        block_share_network: Block_Network_Spec.Network<SignedBeaconBlock>,
        block_created: set<BeaconBlock>,
        construct_randao_reveal: (set<BLSSignature>) -> Optional<BLSSignature>,
        construct_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>,
        all_submitted_signed_blocks: set<SignedBeaconBlock>
    )
    
    datatype Event = 
        | AdversaryTakingStep(
                node: BLSPubkey, 
                new_randao_shares_sent: set<MessaageWithRecipient<RandaoShare>>,
                new_block_shares_sent: set<MessaageWithRecipient<SignedBeaconBlock>>
            )
        | HonestNodeTakingStep(
                node: BLSPubkey, 
                event: Block_Types.Event, 
                nodeOutputs: DVC_Block_Proposer_Spec_NonInstr.Outputs
            )

    predicate complete_randao_reveal_from_dv_pubkey(
        s: DVState
    )
    {
        forall randao_shares: set<RandaoShare> ::
            ( 
                var all_randao_sig := set share | share in randao_shares :: share.signature;
                var constructed_sig := s.construct_randao_reveal(all_randao_sig);                    
                constructed_sig.isPresent() ==>  
                    forall verifiable_randao_shares: set<RandaoShare>, slot: Slot, fork_version: Version |
                        && verifiable_randao_shares <= randao_shares
                        && |verifiable_randao_shares| >= quorum(|s.all_nodes|)
                        && (forall randao_share | randao_share in verifiable_randao_shares :: randao_share.slot ==  slot) 
                                :: && var signing_root := compute_randao_reveal_signing_root(slot);
                                   && verify_bls_signature(signing_root, constructed_sig.safe_get(), s.dv_pubkey)
            )
    }   

    predicate only_one_randao_per_slot(
        s: DVState
    )            
    {
        forall shares1: set<RandaoShare>, shares2: set<RandaoShare> ::
            ( 
                && |shares1| >= quorum(|s.all_nodes|)
                && |shares2| >= quorum(|s.all_nodes|)
                && (exists duty: ProposerDuty, epoch: Epoch, slot: Slot, root: Root ::
                    && ( forall randao_share | randao_share in shares1 ::
                            && randao_share.proposer_duty == duty
                            && randao_share.epoch == epoch
                            && randao_share.slot == slot
                            && randao_share.root == compute_randao_reveal_signing_root(slot))
                    && ( forall randao_share | randao_share in shares2 ::
                            && randao_share.proposer_duty == duty
                            && randao_share.epoch == epoch
                            && randao_share.slot == slot
                            && randao_share.root == compute_randao_reveal_signing_root(slot)))
            )
            ==> ( && var all_randao_sig1 := 
                            set randao_share | randao_share in shares1 :: randao_share.signature;
                  && var all_randao_sig2 := 
                            set randao_share | randao_share in shares2 :: randao_share.signature;
                  && s.construct_randao_reveal(all_randao_sig1).isPresent()
                  && s.construct_randao_reveal(all_randao_sig2).isPresent()
                  && ( s.construct_randao_reveal(all_randao_sig1).safe_get() ==
                       s.construct_randao_reveal(all_randao_sig2).safe_get() )
                )                                                  
    }

    predicate complete_randao_reveal_from_shares(
        s: DVState
    )
    {
        forall randao_shares: set<RandaoShare> ::
                    (( exists verifiable_randao_shares: set<RandaoShare>, 
                              duty: ProposerDuty, 
                              epoch: Epoch, 
                              slot: Slot, 
                              root: Root ::
                                && verifiable_randao_shares <= randao_shares                                
                                && |verifiable_randao_shares| >= quorum(|s.all_nodes|)
                                && (forall randao_share | randao_share in verifiable_randao_shares ::
                                            && randao_share.proposer_duty == duty
                                            && randao_share.epoch == epoch
                                            && randao_share.slot == slot
                                            && randao_share.root == compute_randao_reveal_signing_root(slot)
                                            && exists signer :: 
                                                    && signer in s.all_nodes
                                                    &&  verify_bls_signature(
                                                            slot, 
                                                            randao_share.signature, 
                                                            signer)
                        )
                     )
                     <==> (
                            && var all_randao_sig := 
                                set randao_share | randao_share in randao_shares :: randao_share.signature; 
                            && s.construct_randao_reveal(all_randao_sig).isPresent())        
                          )
    }

    predicate complete_signed_block_from_dv_pubkey(
        s: DVState
    )
    {
        forall block_shares: set<SignedBeaconBlock> ::
            ( 
                var all_block_share_sig := set share | share in block_shares :: share.signature;
                var constructed_sig := s.construct_randao_reveal(all_block_share_sig);                    
                constructed_sig.isPresent() ==>  
                    forall verifiable_block_shares: set<SignedBeaconBlock>, msg: BeaconBlock |
                        && verifiable_block_shares <= block_shares
                        && |verifiable_block_shares| >= quorum(|s.all_nodes|)
                        && (forall block_share | block_share in verifiable_block_shares :: block_share.message == msg) 
                                :: && var signing_root := compute_block_signing_root(msg);
                                   && verify_bls_signature(msg, constructed_sig.safe_get(), s.dv_pubkey)
            )
    }

    
    predicate only_one_complete_signed_block_per_block(
        s: DVState
    )            
    {
        forall shares1: set<SignedBeaconBlock>, shares2: set<SignedBeaconBlock> ::
            ( 
                && |shares1| >= quorum(|s.all_nodes|)
                && |shares2| >= quorum(|s.all_nodes|)
                && ( exists msg: BeaconBlock ::
                        && ( forall block_share | block_share in shares1 :: block_share.message == msg )
                        && ( forall block_share | block_share in shares2 :: block_share.message == msg )   
                   )
            )
            ==> ( 
                  && s.construct_signed_block(shares1).isPresent()    
                  && s.construct_signed_block(shares2).isPresent()
                  && s.construct_signed_block(shares1).safe_get() ==
                     s.construct_signed_block(shares2).safe_get()
                )                                                  
    }

    predicate complete_signed_block_from_block_shares(
        s: DVState
    )
    {
        forall block_shares: set<SignedBeaconBlock> ::
                    (( exists verifiable_block_shares: set<SignedBeaconBlock>, 
                              msg: BeaconBlock ::
                                && verifiable_block_shares <= block_shares                                
                                && |verifiable_block_shares| >= quorum(|s.all_nodes|)
                                && (forall block_share | block_share in verifiable_block_shares ::
                                            && block_share.message == msg                                            
                                            && exists signer :: 
                                                    && signer in s.all_nodes
                                                    &&  verify_bls_signature(
                                                            msg, 
                                                            block_share.signature, 
                                                            signer)
                        )
                     )
                     <==> s.construct_signed_block(block_shares).isPresent())    
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
        // && only_one_randao_per_slot(s)
        && complete_randao_reveal_from_dv_pubkey(s)
        && complete_randao_reveal_from_shares(s)
        // && only_one_complete_signed_block_per_block(s)
        && complete_signed_block_from_dv_pubkey(s)
        && complete_signed_block_from_block_shares(s)
        && s.all_submitted_signed_blocks == {}
        && ( forall pubkey | pubkey in s.honest_nodes_states.Keys ::
                DVC_Block_Proposer_Spec_NonInstr.Init(
                    s.honest_nodes_states[pubkey], 
                    s.dv_pubkey, 
                    s.all_nodes, 
                    s.construct_randao_reveal, 
                    s.construct_signed_block, 
                    initial_block_slashing_db, 
                    pubkey
                ))    
        &&  Block_Network_Spec.Init(s.block_share_network, s.all_nodes)
        &&  ( forall bci | bci in  s.block_consensus_instances.Values ::
                Block_Consensus_Spec.Init(bci, s.all_nodes, s.honest_nodes_states.Keys))                
    }

    predicate Next(
        s: DVState,
        s': DVState 
    )
    {
        exists e :: NextEvent(s, e, s')
    }

    predicate NextEvent(
        s: DVState,
        event: Event,
        s': DVState
    )
    {
        && s'.honest_nodes_states.Keys == s.honest_nodes_states.Keys
        && s'.adversary == s.adversary        
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

    predicate NextHonestNode(
        s: DVState,
        node: BLSPubkey,
        nodeEvent: Block_Types.Event,
        nodeOutputs: DVC_Block_Proposer_Spec_NonInstr.Outputs,
        s': DVState        
    ) 
    {
        && node in s.honest_nodes_states.Keys
        && var s_w_honest_node_states_updated :=
            if nodeEvent.ImportNewBlock? then 
                s.(
                    honest_nodes_states := 
                        s.honest_nodes_states[node := add_signed_block_to_bn(s.honest_nodes_states[node], 
                                                                             nodeEvent.signed_block)]
                )
            else 
                s 
            ;
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
                                               nodeOutputs.randao_shares_sent, 
                                               {randao_share})
                      && Block_Network_Spec.Next(s.block_share_network, 
                                               s'.block_share_network, 
                                               node, 
                                               nodeOutputs.block_shares_sent, 
                                               {}))
            case ReceiveBlockShare(block_share) =>
                    ( && Block_Network_Spec.Next(s.randao_share_network, 
                                               s'.randao_share_network, 
                                               node, 
                                               nodeOutputs.randao_shares_sent, 
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
                                               nodeOutputs.randao_shares_sent, 
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
        forall slot | slot in s.block_consensus_instances.Keys ::
                && var output := 
                        if nodeEvent.BlockConsensusDecided? && nodeEvent.block.slot == slot then 
                            Some(Decided(node, nodeEvent.block))
                        else
                            None
                    ;
                && var validityPredicates := 
                        map nid | && nid in s.honest_nodes_states.Keys 
                                  && slot in s.honest_nodes_states[nid].block_consensus_engine_state.active_block_consensus_instances.Keys
                                        ::
                                            s.honest_nodes_states[nid].block_consensus_engine_state.active_block_consensus_instances[slot].validityPredicate
                    ;
                && Block_Consensus_Spec.Next(
                        s.block_consensus_instances[slot],
                        validityPredicates,
                        s'.block_consensus_instances[slot],
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
    {
        && s'.honest_nodes_states.Keys == s.honest_nodes_states.Keys
        && s'.adversary == s.adversary
        && s'.dv_pubkey == s.dv_pubkey      
        && s'.construct_randao_reveal == s.construct_randao_reveal
        && s'.construct_signed_block == s.construct_signed_block
        && node in s.honest_nodes_states.Keys 
        && var new_node_state := s'.honest_nodes_states[node];
        && DVC_Block_Proposer_Spec_NonInstr.Next(s.honest_nodes_states[node], nodeEvent, new_node_state, nodeOutputs)        
        && s'.honest_nodes_states == s.honest_nodes_states[node := new_node_state]    
        && s'.all_submitted_signed_blocks == s.all_submitted_signed_blocks + nodeOutputs.submitted_signed_blocks    
        && reliable_networks(s, node, nodeEvent, nodeOutputs, s')
        && is_valid_decided_consensus_instance(s, node, nodeEvent, nodeOutputs, s')            
    }

    predicate NextAdversary(
        s: DVState,
        node: BLSPubkey,
        new_wrapped_randao_shares_sent: set<MessaageWithRecipient<RandaoShare>>,
        new_wrapped_block_shares_sent: set<MessaageWithRecipient<SignedBeaconBlock>>,
        s': DVState
    )
    {
        && s'.honest_nodes_states.Keys == s.honest_nodes_states.Keys
        && s'.adversary == s.adversary
        && s'.dv_pubkey == s.dv_pubkey      
        && s'.construct_randao_reveal == s.construct_randao_reveal
        && s'.construct_signed_block == s.construct_signed_block
        && node in (s.all_nodes - s.honest_nodes_states.Keys)
        && node in s.adversary.nodes
        && ( forall msg :: msg in new_wrapped_randao_shares_sent 
                ==> verify_bls_signature(msg.message.slot, msg.message.signature, node)                     
           )
        && ( forall msg :: msg in new_wrapped_block_shares_sent 
                ==> verify_bls_signature(msg.message.message, msg.message.signature, node)                     
           )
        && Block_Network_Spec.Next(
                s.randao_share_network, 
                s'.randao_share_network, 
                node, 
                new_wrapped_randao_shares_sent, 
                {})
        && Block_Network_Spec.Next(
                s.block_share_network, 
                s'.block_share_network, 
                node, 
                new_wrapped_block_shares_sent, 
                {})
        && s.all_submitted_signed_blocks <= s'.all_submitted_signed_blocks
        && s' == s.(honest_nodes_states := s'.honest_nodes_states,
                    randao_share_network := s'.randao_share_network,
                    block_share_network := s'.block_share_network,
                    block_consensus_instances := s'.block_consensus_instances,
                    all_submitted_signed_blocks := s'.all_submitted_signed_blocks
                   )        
    }
}