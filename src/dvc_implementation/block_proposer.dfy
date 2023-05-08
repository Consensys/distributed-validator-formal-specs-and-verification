include "../common/commons.dfy"
include "./dvc_externs.dfy"

abstract module Block_DVC_Implementation
{
    import opened Types
    import opened CommonFunctions
    import opened DVC_Externs : DVC_Externs

    export PublicInterface
        reveals  Block_DVC        
        provides Block_DVC.process_event,
                 Block_DVC.getRepr,
                 Block_DVC.ValidRepr,
                 Block_DVC.ValidConstructorRepr                                   
        provides Types, 
                 DVC_Externs

    class Block_DVC {        
        var current_proposer_duty: Optional<ProposerDuty>;
        var latest_proposer_duty: Optional<ProposerDuty>;
        var rcvd_randao_shares: map<Slot, set<RandaoShare>>;
        var rcvd_block_shares: map<Slot, map<BeaconBlock, set<SignedBeaconBlock>>>;
        var randao_shares_to_broadcast: map<Slot, RandaoShare>
        var block_shares_to_broadcast: map<Slot, SignedBeaconBlock> 
        var construct_complete_signed_randao_reveal: (set<BLSSignature>) -> Optional<BLSSignature>;
        var construct_complete_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>;
        var peers: set<BLSPubkey>;      // set of BLS pubkeys of all DVCs
        var dv_pubkey: BLSPubkey;       // its own BLS pubkey
        var future_consensus_instances_on_blocks_already_decided: map<Slot, BeaconBlock>;    // known blocks for future slots

        var slashing_db: SlashingDB<SlashingDBBlock>;
        const block_consensus: Consensus<BeaconBlock, SlashingDBBlock>;
        const network : Network
        const bn: BeaconNode<SignedBeaconBlock>;
        const rs: RemoteSigner;
        
        
                 
        constructor(
            pubkey: BLSPubkey, 
            dv_pubkey: BLSPubkey,
            block_consensus: Consensus<BeaconBlock, SlashingDBBlock>, 
            peers: set<BLSPubkey>,
            network: Network,
            bn: BeaconNode<SignedBeaconBlock>,
            rs: RemoteSigner,
            initial_slashing_db: SlashingDB<SlashingDBBlock>,
            construct_complete_signed_randao_reveal: (set<BLSSignature>) -> Optional<BLSSignature>,
            construct_complete_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>
        )
        requires block_consensus.consensus_instances_started == map[]
        requires ValidConstructorRepr(block_consensus, network, bn, rs, initial_slashing_db)
        {
            this.current_proposer_duty := None;
            this.latest_proposer_duty := None;
            this.slashing_db := initial_slashing_db;
            this.randao_shares_to_broadcast := map[];
            this.block_shares_to_broadcast := map[];
            this.rcvd_randao_shares := map[];
            this.rcvd_block_shares := map[];
            this.future_consensus_instances_on_blocks_already_decided := map[];
            
            
            
            
            
            this.block_consensus := block_consensus;
            this.peers := peers;
            this.network := network;
            this.rs := rs;
            this.bn := bn;
            this.construct_complete_signed_block := construct_complete_signed_block;
            this.construct_complete_signed_randao_reveal := construct_complete_signed_randao_reveal;
            this.dv_pubkey := dv_pubkey;
        }

        // The only public method
        method process_event(
            event: BlockEvent
        ) returns (s: Status)
        requires ValidRepr()
        modifies getRepr()
        {
            match event {
                case ServeProposerDuty(proposer_duty) => 
                    :- serve_proposer_duty(proposer_duty);
                case BlockConsensusDecided(id, block) => 
                    :- block_consensus_decided(id, block);
                case ReceiveRandaoShare(randao_share) => 
                    :- listen_for_randao_shares(randao_share);
                case ReceiveSignedBeaconBlock(block_share) => 
                    listen_for_block_signature_shares(block_share);                    
                case ImportedNewBlock(block) => 
                    :- listen_for_new_imported_blocks(block);
                case ResendRandaoRevealSignatureShare => 
                    resend_randao_share();                    
                case ResendBlockShare => 
                    resend_block_share();
                case NoEvent =>
                    
            }

            {return Success;}
        }   

        // Multiple proposer duties may be in queue.
        // The processing of a new duty is postponed if the last consensus instance has not reached 
        // an agreement.
        // Multiple consensus instances can run simultaneously but at most one has not decided a value.
        // New: a randao share is broadcased immediately after a DVC receives a new proposer duty.
        // This update is to reduce a delay in processing a new duty.
        method serve_proposer_duty(
            proposer_duty: ProposerDuty
        ) returns (s: Status)
        requires ValidRepr()
        modifies getRepr()
        ensures ValidRepr()
        {
            terminate_current_proposer_duty();
            current_proposer_duty := Some(proposer_duty);
            latest_proposer_duty := Some(proposer_duty);
            :- broadcast_randao_share(proposer_duty);         

            return Success;
        }

        method terminate_current_proposer_duty() 
        requires ValidRepr()
        modifies getRepr()
        ensures ValidRepr()
        {
            current_proposer_duty := None;
        }

        // broadcast_randao_share is for lines 166 - 171.
        method broadcast_randao_share(
            proposer_duty: ProposerDuty
        ) returns (s: Status)
        // requires this.latest_proposer_duty.isPresent()
        requires ValidRepr()
        modifies getRepr()
        ensures ValidRepr()
        {            
            var slot := proposer_duty.slot;
            var fork_version := bn.get_fork_version(slot);
            var epoch := compute_epoch_at_slot(slot);            
            var root := compute_randao_reveal_signing_root(slot);
            var randao_signature := rs.sign_randao_reveal(epoch, fork_version, root);                                                           
            var randao_share := 
                RandaoShare(
                    proposer_duty := proposer_duty,
                    slot := slot,
                    signing_root := root,
                    signature := randao_signature
                );
            randao_shares_to_broadcast := randao_shares_to_broadcast[proposer_duty.slot := randao_share];
            network.send_randao_share(randao_share, peers);    

            :- check_for_next_duty(proposer_duty);

            return Success;
        }

        method check_for_next_duty(
            proposer_duty: ProposerDuty
        ) returns (s: Status)
        requires this.latest_proposer_duty.isPresent()
        requires ValidRepr()
        modifies getRepr()
        ensures ValidRepr()
        {            
            var slot := proposer_duty.slot;
            if slot in future_consensus_instances_on_blocks_already_decided
            {
                var block := this.future_consensus_instances_on_blocks_already_decided[slot];                
                update_block_slashing_db(block, dv_pubkey);
                future_consensus_instances_on_blocks_already_decided := future_consensus_instances_on_blocks_already_decided - {slot};
            }
            else 
            {                    
                :- start_consensus_if_can_construct_randao_share();  
            }                                

            return Success;            
        }

        // TODO: think of a better name
        // start_consensus_if_can_construct_randao_share is for lines 172 - 173.
        // validityCheck is to ensure the desired properties of a consensus instance.
        method start_consensus_if_can_construct_randao_share() returns (s: Status)
        requires ValidRepr()
        modifies getRepr()      
        ensures ValidRepr()  
        {
            if  && current_proposer_duty.isPresent()
                && current_proposer_duty.safe_get().slot in rcvd_randao_shares
            {
                var proposer_duty := this.current_proposer_duty.safe_get();
                var all_rcvd_randao_sig := 
                    set randao_share | randao_share in this.rcvd_randao_shares[
                                                this.current_proposer_duty.safe_get().slot]
                                                    :: randao_share.signature;                
                var constructed_randao_reveal := this.construct_complete_signed_randao_reveal(all_rcvd_randao_sig);

                if constructed_randao_reveal.isPresent()  
                {
                    var validityCheck := new BlockConsensusValidityCheck(dv_pubkey, slashing_db, current_proposer_duty.safe_get(), constructed_randao_reveal.safe_get());
                    { :- block_consensus.start(current_proposer_duty.safe_get().slot, validityCheck); }
                }   

                return Success;                 
            }            
        }

        // Check whether messages related to slot should be processed.
        predicate method is_slot_for_current_or_future_instances(
            active_consensus_instances_on_beacon_blocks: set<Slot>,
            received_slot: Slot
        )
        reads this
        {
            // TODO: The check below is not consistent with the clean-up operation done in
            // listen_for_new_imported_blocks. Here, any share for future slot is accepted, whereas
            // listen_for_new_imported_blocks cleans up the received shares for any already-decided slot. This
            // inconsistency should be fixed up by either accepting here only shares with slot higher than the
            // maximum already-decided slot or changing the clean-up code in listen_for_new_imported_blocks to clean
            // up only slot lower thant the slot of the current/latest duty.

            || (active_consensus_instances_on_beacon_blocks == {} && !latest_proposer_duty.isPresent())
            || (active_consensus_instances_on_beacon_blocks != {} && get_min(active_consensus_instances_on_beacon_blocks) <= received_slot)
            || (active_consensus_instances_on_beacon_blocks == {} && current_proposer_duty.isPresent() && current_proposer_duty.safe_get().slot <= received_slot)                
            || (active_consensus_instances_on_beacon_blocks == {} && !current_proposer_duty.isPresent() && latest_proposer_duty.isPresent() && latest_proposer_duty.safe_get().slot < received_slot)            
        }

        // listen_for_randao_shares is an underlying method for line 172.
        method listen_for_randao_shares(
            randao_share: RandaoShare
        ) returns (s: Status)   
        requires ValidRepr()
        modifies getRepr()
        {
            var slot := randao_share.slot;
            var active_consensus_instances_on_beacon_blocks := block_consensus.get_active_instances();

            if is_slot_for_current_or_future_instances(active_consensus_instances_on_beacon_blocks, slot)
            {
                rcvd_randao_shares := rcvd_randao_shares[slot := getOrDefault(rcvd_randao_shares, slot, {}) + {randao_share} ]; 
                :- start_consensus_if_can_construct_randao_share(); 
            }

            return Success;                            
        }        

        // update_block_slashing_db is for line 177.
        method update_block_slashing_db(block: BeaconBlock, pubkey: BLSPubkey)
        requires ValidRepr()
        modifies slashing_db.Repr
        ensures fresh(slashing_db.Repr - old(slashing_db.Repr))
        ensures  ValidRepr()
        {   
            var newDBBlock := construct_SlashingDBBlock_from_beacon_block(block);
            slashing_db.add_record(newDBBlock, dv_pubkey);                
        }        

        // block_consensus_decided is for lines 173 - 182.
        method block_consensus_decided(            
            id: Slot,
            block: BeaconBlock
        ) returns (r: Status)
        requires ValidRepr()
        modifies getRepr()              
        {              
            if  && current_proposer_duty.isPresent()
                && current_proposer_duty.safe_get().slot == block.slot
            {
            update_block_slashing_db(block, current_proposer_duty.safe_get().pubkey);
            var block_signing_root := compute_block_signing_root(block);
            var fork_version := bn.get_fork_version(block.slot);
            var block_signature := rs.sign_block(block, fork_version, block_signing_root);
            var block_share := SignedBeaconBlock(block, block_signature);
            block_shares_to_broadcast := block_shares_to_broadcast[current_proposer_duty.safe_get().slot := block_share];
            network.send_block_share(block_share, peers); 

            current_proposer_duty := None;
            }
        }

        // listen_for_block_signature_shares is for lines 217 - 230.
        method listen_for_block_signature_shares(block_share: SignedBeaconBlock)
        requires ValidRepr()
        modifies getRepr()
        {

            var active_consensus_instances_on_beacon_blocks := block_consensus.get_active_instances();
            var slot := block_share.block.slot;

            if is_slot_for_current_or_future_instances(active_consensus_instances_on_beacon_blocks, slot)
            {
                var data := block_share.block;
                var rcvd_block_shares_db_at_slot := getOrDefault(rcvd_block_shares, slot, map[]);
                rcvd_block_shares := 
                    rcvd_block_shares[
                        slot := 
                            rcvd_block_shares_db_at_slot[
                                        data := 
                                            getOrDefault(rcvd_block_shares_db_at_slot, data, {}) + 
                                            {block_share}
                                        ]
                            ];
                            
                if construct_complete_signed_block(rcvd_block_shares[slot][data]).isPresent()
                {
                    var complete_signed_block := construct_complete_signed_block(rcvd_block_shares[slot][data]).safe_get();  
                    bn.submit_data(complete_signed_block);  
                }
            } 
        }

        method listen_for_new_imported_blocks_helper(
            consensus_instances_on_blocks_already_decided: map<Slot, BeaconBlock>
        ) returns (new_consensus_instances_on_blocks_already_decided: map<Slot, BeaconBlock>)
        {
            if this.latest_proposer_duty.isPresent()
            {
                var old_instances := 
                        set i | 
                            && i in consensus_instances_on_blocks_already_decided.Keys
                            && i <= this.latest_proposer_duty.safe_get().slot
                        ;
                return consensus_instances_on_blocks_already_decided - old_instances;
            }
            else
            {
                return consensus_instances_on_blocks_already_decided;
            }
        }

        // A new method to ensure the liveness property.
        method listen_for_new_imported_blocks(
            block: BeaconBlock
        ) returns (r: Status)
        // requires block.body.state_root in this.bn.state_roots_of_imported_blocks
        requires ValidRepr()
        modifies getRepr()
        {
            var new_consensus_instances_on_blocks_already_decided: map<Slot, BeaconBlock> := 
                map[ block.slot := block ];

            var consensus_instances_on_blocks_already_decided := this.future_consensus_instances_on_blocks_already_decided + new_consensus_instances_on_blocks_already_decided;

            var future_consensus_instances_on_blocks_already_decided := 
                listen_for_new_imported_blocks_helper(consensus_instances_on_blocks_already_decided);

            this.block_consensus.stop_multiple(future_consensus_instances_on_blocks_already_decided.Keys);
            this.block_shares_to_broadcast := this.block_shares_to_broadcast - consensus_instances_on_blocks_already_decided.Keys;
            this.rcvd_block_shares := this.rcvd_block_shares - consensus_instances_on_blocks_already_decided.Keys;                   
            this.block_consensus.stop_multiple(consensus_instances_on_blocks_already_decided.Keys);

            if  && this.current_proposer_duty.isPresent() 
                && this.current_proposer_duty.safe_get().slot in consensus_instances_on_blocks_already_decided 
            {
                var decided_beacon_blocks := consensus_instances_on_blocks_already_decided[this.current_proposer_duty.safe_get().slot];
                update_block_slashing_db(decided_beacon_blocks, this.dv_pubkey);                 
            }
            
            return Success;  
        }

        method resend_randao_share()
        requires ValidRepr()
        modifies getRepr()
        {
            network.send_randao_shares(randao_shares_to_broadcast.Values, peers);
        }        

        method resend_block_share()
        requires ValidRepr()
        modifies getRepr()
        {
            network.send_block_shares(block_shares_to_broadcast.Values, peers);
        }  

        // For the verification purposes only.
        static predicate ValidConstructorRepr(
            block_consensus: Consensus<BeaconBlock, SlashingDBBlock>, 
            network: Network,
            bn: BeaconNode<SignedBeaconBlock>,
            rs: RemoteSigner ,
            slashing_db: SlashingDB           
        )
        reads *
        {
            && ( block_consensus.consensus_instances_started.Values 
                 !! bn.Repr !! network.Repr !! block_consensus.Repr !! rs.Repr
                 !! slashing_db.Repr )
            && bn.Valid()
            && rs.Valid()
            && network.Valid()
            && block_consensus.Valid() 
            && slashing_db.Valid()                               
        }   

        // For the verification purposes only.
        function getChildrenRepr(): set<object?>
        reads *
        {
            this.block_consensus.consensus_instances_started.Values 
            + this.bn.Repr + this.network.Repr + this.block_consensus.Repr + this.rs.Repr
            + this.slashing_db.Repr
        }        

        // For the verification purposes only.
        function getRepr(): set<object?>
        reads *
        {
            getChildrenRepr() + {this}
        }

        // For the verification purposes only.
        predicate ValidRepr()
        reads *
        {
            && ValidConstructorRepr(this.block_consensus, this.network, this.bn, this.rs, this.slashing_db)
            && this !in getChildrenRepr()                                
        }             
    }    

    class BlockConsensusValidityCheck extends ConsensusValidityCheck<BeaconBlock, SlashingDBBlock>
    {
        const dv_pubkey: BLSPubkey
        const proposer_duty: ProposerDuty
        const randao_reveal: BLSSignature

        constructor(
            dv_pubkey: BLSPubkey,
            slashind_db: SlashingDB<SlashingDBBlock>,
            proposer_duty: ProposerDuty,
            randao_reveal: BLSSignature
        )
        requires slashind_db.Valid()
        ensures this.dv_pubkey == dv_pubkey
        ensures this.proposer_duty == proposer_duty
        ensures this.slashing_db == slashind_db
        ensures this.randao_reveal == randao_reveal
        ensures Valid()
        {
            this.dv_pubkey := dv_pubkey;
            this.proposer_duty := proposer_duty;
            this.slashing_db := slashind_db;
            this.randao_reveal := randao_reveal;            
            Repr := {this} + {slashing_db} + slashind_db.Repr;
        }

        method is_valid(data: BeaconBlock) returns (valid: bool)
        requires Valid()
        modifies Repr
        ensures Valid()
        ensures fresh(Repr - old(Repr))
        {
            assert Valid();
            assert slashing_db.Valid();
            var attestations := slashing_db.get_records(dv_pubkey);
            Repr := Repr + slashing_db.Repr;

            valid := ci_decision_is_valid_beacon_block(attestations, data, proposer_duty, randao_reveal);             
        }        
    }    
}
