include "../../common/block_proposer/block_types.dfy"
include "../../common/block_proposer/block_common_functions.dfy"
include "../../common/block_proposer/block_signing_functions.dfy"
include "./block_dvc_externs.dfy"

abstract module Block_DVC_Impl
{
    import opened Block_Types
    import opened Block_Common_Functions
    import opened Block_Signing_Functions
    import opened Block_DVC_Externs

    export PublicInterface
        reveals  Block_DVC        
        provides Block_DVC.process_event,
                 Block_DVC.getRepr,
                 Block_DVC.ValidRepr,
                 Block_DVC.ValidConstructorRepr                                   
        provides Block_Types, 
                 Block_Common_Functions,
                 Block_Signing_Functions,
                 Block_DVC_Externs

    class Block_DVC {        
        const bn: BeaconNode;
        const consensus_on_block: Consensus<BeaconBlock>;
        const network : Network
        const rs: RemoteSigner;
        var dv_pubkey: BLSPubkey;       // its own BLS pubkey
        var peers: set<BLSPubkey>;      // set of BLS pubkeys of all DVCs

        var future_decided_slots: map<Slot, BeaconBlock>    // known blocks for future slots
        var block_shares_to_broadcast: map<Slot, SignedBeaconBlock> 
        var randao_shares_to_broadcast: map<Slot, RandaoShare>
        var complete_block_signature: (set<SignedBeaconBlock>) -> Optional<BLSSignature>;
        // must satisfy properties of M-of-N threshold signatures 
        
        var slashing_db: SlashingDB;
        var block_share_db: BlockSignatureShareDB;

        var rcvd_randao_shares: map<Slot, set<RandaoShare>>;
        var rcvd_block_shares: map<Slot, map<BeaconBlock, set<SignedBeaconBlock>>>;

        var construct_signed_randao_reveal: (set<BLSSignature>) -> Optional<BLSSignature>;
        var construct_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>;
        // must satisfy properties of M-of-N threshold signatures 
        
        var current_proposer_duty: Optional<ProposerDuty>;
        var last_served_proposer_duty: Optional<ProposerDuty>;
                 
        constructor(
            bn: BeaconNode,
            consensus_on_block: Consensus<BeaconBlock>, 
            network: Network,            
            rs: RemoteSigner,                        
            dv_pubkey: BLSPubkey,
            peers: set<BLSPubkey>,            
            complete_block_signature: (set<SignedBeaconBlock>) -> Optional<BLSSignature>,
            construct_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>,
            construct_signed_randao_reveal: (set<BLSSignature>) -> Optional<BLSSignature>,
            initial_slashing_db: SlashingDB
        )
        requires consensus_on_block.consensus_instances_started == map[]
        requires ValidConstructorRepr(consensus_on_block, network, bn, rs, initial_slashing_db)        
        {            
            this.future_decided_slots := map[];

            this.block_shares_to_broadcast := map[];
            this.randao_shares_to_broadcast := map[];
            this.slashing_db := initial_slashing_db;
            this.block_share_db := map[];    
            this.rcvd_randao_shares := map[];   
            this.rcvd_block_shares := map[];   
            this.current_proposer_duty := None;
            this.last_served_proposer_duty := None;
            
            this.bn := bn;
            this.consensus_on_block := consensus_on_block;
            this.network := network;
            this.rs := rs;

            this.dv_pubkey := dv_pubkey;
            this.peers := peers;
            
            this.complete_block_signature := complete_block_signature;
            this.construct_signed_block := construct_signed_block;
            this.construct_signed_randao_reveal := construct_signed_randao_reveal;
        }

        // The only public method
        method process_event(
            event: Event
        ) 
        requires ValidRepr()
        modifies getRepr()
        {
            match event {
                case ServeProposerDuty(proposer_duty) => 
                    serve_proposer_duty(proposer_duty);
                case BlockConsensusDecided(block) => 
                    block_consensus_decided(block);
                case ReceiveRandaoShare(randao_share) => 
                    listen_for_randao_shares(randao_share);
                case ReceiveBlockShare(block_share) => 
                    listen_for_block_shares(block_share);                    
                case ImportNewBlock(block) => 
                    listen_for_new_imported_blocks(block);
                case ResendRandaoShare => 
                    resend_randao_share();                    
                case ResendBlockShare => 
                    resend_block_share();
                case NoEvent =>
                    
            }
        }   

        // Multiple proposer duties may be in queue.
        // The processing of a new duty is postponed if the last consensus instance has not reached 
        // an agreement.
        // Multiple consensus instances can run simultaneously but at most one has not decided a value.
        // New: a randao share is broadcased immediately after a DVC receives a new proposer duty.
        // This update is to reduce a delay in processing a new duty.
        method serve_proposer_duty(
            proposer_duty: ProposerDuty
        ) 
        requires ValidRepr()
        modifies getRepr()
        {
            terminate_current_proposer_duty();
            broadcast_randao_share(proposer_duty);
            { check_for_next_queued_duty(proposer_duty); }          
        }

        method terminate_current_proposer_duty() 
        requires ValidRepr()
        modifies getRepr()
        {
            current_proposer_duty := None;
        }

        // broadcast_randao_share is for lines 166 - 171.
        method broadcast_randao_share(serving_duty: ProposerDuty)
        requires ValidRepr()
        modifies getRepr()
        {            
            var slot := serving_duty.slot;
            var epoch := compute_epoch_at_slot(slot);            
            var fork_version := bn.get_fork_version(slot);    
            var root := compute_randao_reveal_signing_root(slot);
            var randao_signature := rs.sign_randao_reveal(epoch, fork_version, root);                                                           
            var randao_share := RandaoShare(serving_duty, epoch, slot, root, randao_signature);
            randao_shares_to_broadcast := randao_shares_to_broadcast[serving_duty.slot := randao_share];
            network.send_randao_share(randao_share, peers);            
        }

        method check_for_next_queued_duty(serving_duty: ProposerDuty)
        requires ValidRepr()
        modifies getRepr()
        {            
            
            var slot := serving_duty.slot;
            if slot in future_decided_slots
            {
                update_block_slashing_db(future_decided_slots[slot], dv_pubkey);
                future_decided_slots := future_decided_slots - {slot};
            }
            else 
            {                    
                current_proposer_duty := Some(serving_duty);
                last_served_proposer_duty := Some(serving_duty);
                start_consensus_if_can_construct_randao_share();  
            }                                
            
        }

        // TODO: think of a better name
        // start_consensus_if_can_construct_randao_share is for lines 172 - 173.
        // validityCheck is to ensure the desired properties of a consensus instance.
        method start_consensus_if_can_construct_randao_share()
        requires ValidRepr()
        modifies getRepr()        
        {
            if  && current_proposer_duty.isPresent()
                && current_proposer_duty.safe_get().slot in rcvd_randao_shares
            {
                var all_rcvd_randao_sig := 
                        set randao_share | randao_share in rcvd_randao_shares[current_proposer_duty.safe_get().slot]
                                            :: randao_share.signature;
                var constructed_randao_reveal := construct_signed_randao_reveal(all_rcvd_randao_sig);

                if constructed_randao_reveal.isPresent()  
                {
                    var validityCheck := new BlockConsensusValidityCheck(dv_pubkey, slashing_db, current_proposer_duty.safe_get(), constructed_randao_reveal.safe_get());
                    consensus_on_block.start(
                        current_proposer_duty.safe_get().slot,
                        validityCheck
                    );
                }                    
            }            
        }

        // Check whether messages related to slot should be processed.
        predicate method is_slot_for_current_or_future_instances(
            active_block_consensus_instances: set<Slot>,
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

            || (active_block_consensus_instances == {} && !last_served_proposer_duty.isPresent())
            || (active_block_consensus_instances != {} && get_min(active_block_consensus_instances) <= received_slot)
            || (active_block_consensus_instances == {} && current_proposer_duty.isPresent() && current_proposer_duty.safe_get().slot <= received_slot)                
            || (active_block_consensus_instances == {} && !current_proposer_duty.isPresent() && last_served_proposer_duty.isPresent() && last_served_proposer_duty.safe_get().slot < received_slot)            
        }

        // listen_for_randao_shares is an underlying method for line 172.
        method listen_for_randao_shares(
            randao_share: RandaoShare
        )         
        // requires current_proposer_duty.isPresent() ==> current_proposer_duty.safe_get().slot !in consensus_on_block.consensus_instances_started
        requires ValidRepr()
        modifies getRepr()
        {
            var slot := randao_share.slot;
            var active_block_consensus_instances := consensus_on_block.get_active_instances();

            if is_slot_for_current_or_future_instances(active_block_consensus_instances, slot)
            {
                rcvd_randao_shares := rcvd_randao_shares[slot := getOrDefault(rcvd_randao_shares, slot, {}) + {randao_share} ]; 
                start_consensus_if_can_construct_randao_share();      
            }                                         
        }        

        // update_block_slashing_db is for line 177.
        method update_block_slashing_db(block: BeaconBlock, pubkey: BLSPubkey)
        requires ValidRepr()
        modifies slashing_db.Repr
        ensures fresh(slashing_db.Repr - old(slashing_db.Repr))
        ensures  ValidRepr()
        {   
            var newDBBlock := SlashingDBBlock(block.slot, hash_tree_root(block));
            slashing_db.add_proposal(newDBBlock, dv_pubkey);                
        }        

        // block_consensus_decided is for lines 173 - 182.
        method block_consensus_decided(            
            block: BeaconBlock
        )
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

        // listen_for_block_shares is for lines 217 - 230.
        method listen_for_block_shares(block_share: SignedBeaconBlock)
        requires ValidRepr()
        modifies getRepr()
        {

            var active_block_consensus_instances := consensus_on_block.get_active_instances();
            var slot := block_share.message.slot;

            if is_slot_for_current_or_future_instances(active_block_consensus_instances, slot)
            {
                var data := block_share.message;
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
                            
                if construct_signed_block(rcvd_block_shares[slot][data]).isPresent()
                {
                    var complete_signed_block := construct_signed_block(rcvd_block_shares[slot][data]).safe_get();  
                    bn.submit_signed_block(complete_signed_block);  
                }
            } 
        }

        // A new method to ensure the liveness property.
        method listen_for_new_imported_blocks(
            signed_block: SignedBeaconBlock
        ) 
        requires ValidRepr()
        modifies getRepr()
        {
            var block_consensus_already_decided := future_decided_slots;
            if verify_bls_signature(signed_block.message, signed_block.signature, dv_pubkey)
            {
                block_consensus_already_decided := block_consensus_already_decided[signed_block.message.slot := signed_block.message];
            } 

            // TODO: The clean-up below is not consistent with the check done in
            // is_slot_for_current_or_future_instances. See comment in listen_for_attestation_shares for an explanation. 
            block_shares_to_broadcast := block_shares_to_broadcast - block_consensus_already_decided.Keys;
            rcvd_block_shares := rcvd_block_shares - block_consensus_already_decided.Keys;
            randao_shares_to_broadcast := randao_shares_to_broadcast - block_consensus_already_decided.Keys;
            rcvd_randao_shares := rcvd_randao_shares - block_consensus_already_decided.Keys;
            consensus_on_block.stop_multiple(block_consensus_already_decided.Keys);
            
            if last_served_proposer_duty.isPresent() 
            {
                var slot := last_served_proposer_duty.safe_get().slot;
                
                var old_instances := 
                        set i | 
                            && i in block_consensus_already_decided 
                            && i <= last_served_proposer_duty.safe_get().slot
                        ;

                future_decided_slots := block_consensus_already_decided - old_instances;
            }          
            else
            {
                future_decided_slots := block_consensus_already_decided;
            }       

            if current_proposer_duty.isPresent() && current_proposer_duty.safe_get().slot in block_consensus_already_decided.Keys
            {
                update_block_slashing_db(block_consensus_already_decided[current_proposer_duty.safe_get().slot], dv_pubkey);
                current_proposer_duty := None;
            }      
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
            consensus_on_block: Consensus<BeaconBlock>, 
            network: Network,
            bn: BeaconNode,
            rs: RemoteSigner ,
            slashing_db: SlashingDB           
        )
        reads *
        {
            && ( consensus_on_block.consensus_instances_started.Values 
                 !! bn.Repr !! network.Repr !! consensus_on_block.Repr !! rs.Repr
                 !! slashing_db.Repr )
            && bn.Valid()
            && rs.Valid()
            && network.Valid()
            && consensus_on_block.Valid() 
            && slashing_db.Valid()                               
        }   

        // For the verification purposes only.
        function getChildrenRepr(): set<object?>
        reads *
        {
            this.consensus_on_block.consensus_instances_started.Values 
            + this.bn.Repr + this.network.Repr + this.consensus_on_block.Repr + this.rs.Repr
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
            && ValidConstructorRepr(this.consensus_on_block, this.network, this.bn, this.rs, this.slashing_db)
            && this !in getChildrenRepr()                                
        }             
    }    

    class BlockConsensusValidityCheck extends ConsensusValidityCheck<BeaconBlock>
    {
        const dv_pubkey: BLSPubkey
        const proposer_duty: ProposerDuty
        const randao_reveal: BLSSignature

        constructor(
            dv_pubkey: BLSPubkey,
            slashind_db: SlashingDB,
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
            var attestations := slashing_db.get_proposals(dv_pubkey);
            Repr := Repr + slashing_db.Repr;

            valid := consensus_is_valid_beacon_block(attestations, data, proposer_duty, randao_reveal);             
        }        
    }    
}
