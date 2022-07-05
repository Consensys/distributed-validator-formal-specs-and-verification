include "../utils/types.dfy"
include "../utils/common-functions.dfy"
include "../utils/signing-functions.dfy"
include "./externs.dfy"

abstract module DVCNode_Implementation
{
    import opened Types
    import opened CommonFunctions
    import opened SigningFunctions
    import opened DVC_Externs

    export PublicInterface
        reveals  DVC
        /*
        provides DVC.serve_attestation_duty, 
                 DVC.att_consensus_decided, 
                 DVC.listen_for_attestation_shares,
                 DVC.listen_for_new_imported_blocks,
                 DVC.resend_attestation_share,
                 DVC.bn
                 */
        provides Types, 
                 CommonFunctions,
                 SigningFunctions,
                 DVC_Externs

    class DVC {        
        const bn: BeaconNode;
        var consensus_on_block: Consensus;
        var network : Network
        const rs: RemoteSigner;
        var dv_pubkey: BLSPubkey;
        var peers: set<BLSPubkey>;

        
        // var all_proposer_duties: set<ProposerDuty>;
        var proposer_duty_queue: seq<ProposerDuty>;
        var future_decided_slots: set<Slot>   
        var past_decided_slots: set<Slot>;


        var block_sign_share_to_broadcast: Optional<SignedBeaconBlock>
        var complete_block_signature: (set<SignedBeaconBlock>) -> Optional<BLSSignature>;
        
        
        var block_slashing_db: BlockSlashingDB;
        var block_share_db: BlockSignatureShareDB;

        var rcvd_randao_share: map<Slot, set<RandaoShare>>;
        var rcvd_block_share: map<Slot, set<SignedBeaconBlock>>;

        var construct_signed_randao_reveal: (set<RandaoShare>) -> Optional<BLSSignature>;
        var construct_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>;

        var current_proposer_duty: Optional<ProposerDuty>;
        // var last_served_proposer_duty: Optional<ProposerDuty>;
                 
        constructor(
            bn: BeaconNode,
            consensus_on_block: Consensus, 
            network: Network,            
            rs: RemoteSigner,                        
            dv_pubkey: BLSPubkey,
            peers: set<BLSPubkey>,            
            complete_block_signature: (set<SignedBeaconBlock>) -> Optional<BLSSignature>,
            construct_signed_block: (set<SignedBeaconBlock>) -> Optional<SignedBeaconBlock>,
            construct_signed_randao_reveal: (set<RandaoShare>) -> Optional<BLSSignature>,
            M: nat
        )
        requires |peers| > 0
        {            
            this.proposer_duty_queue := [];
            this.future_decided_slots := {};
            this.past_decided_slots := {};

            this.block_sign_share_to_broadcast := None;
            this.block_slashing_db := map[];
            this.block_share_db := map[];    
            this.rcvd_randao_share := map[];   
            this.current_proposer_duty := None;
            // this.last_served_proposer_duty := None;
            
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

        // Only put a new proposer duty in the queue.
        method serve_proposer_duty(
            proposer_duty: ProposerDuty
        )
        modifies this
        {
            proposer_duty_queue := proposer_duty_queue + [proposer_duty];
            var slot := proposer_duty.slot;
            var epoch := compute_epoch_at_slot(slot);
            
            var fork_version := bn.get_fork_version(slot);    
            var root := compute_randao_reveal_signing_root(slot);
            var randao_signature := rs.sign_randao_reveal(epoch, fork_version, root);                                                           
            var randao_share := RandaoShare(proposer_duty, epoch, slot, root, randao_signature);
            network.send_randao_share(randao_share, peers);
        }

        method listen_for_randao_shares(
            randao_share: RandaoShare
        ) 
        requires |peers| > 0
        modifies this
        {
            var slot := randao_share.slot;
            rcvd_randao_share := rcvd_randao_share[slot := getOrDefault(rcvd_randao_share, slot, {}) + {randao_share} ];                      
            check_for_next_queued_duty();
        }

        method {:extern} check_for_next_queued_duty()
        modifies this
        decreases proposer_duty_queue
        {            
            if proposer_duty_queue != []
            {
                var slot := proposer_duty_queue[0].slot;
                if slot in future_decided_slots
                {
                    proposer_duty_queue := proposer_duty_queue[1..];
                    check_for_next_queued_duty();
                }
                else if !current_proposer_duty.isPresent() && 
                        slot in rcvd_randao_share.Keys
                {                    
                    if construct_signed_randao_reveal(rcvd_randao_share[slot]).isPresent()                    
                    {
                        var queue_head := proposer_duty_queue[0];
                        proposer_duty_queue := proposer_duty_queue[1..];
                        start_consensus_on_block(queue_head);
                    }
                }                                
            }     
        }

        method start_consensus_on_block(serving_duty: ProposerDuty)
        modifies this
        {
            current_proposer_duty := Some(serving_duty);
            consensus_on_block.start(serving_duty.slot);                                 
        }

        method {:extern} consensus_is_valid_block(
            block: BeaconBlock,
            proposer_duty: ProposerDuty,
            complete_signed_randao_reveal: BLSSignature)
        returns (b: bool)
        modifies this 
        {
            // TODO: Add correct block.proposer_index check
            var slashable: bool;
            slashable := is_slashable_block(block, proposer_duty.pubkey);
            b := block.slot == proposer_duty.slot &&            
                 block.body.randao_reveal == complete_signed_randao_reveal &&
                 !slashable;                 
        }

        method {:extern} decide_block(block: BeaconBlock)
        modifies this        
        {   
            var slot := block.slot;
            
            if (slot in rcvd_randao_share.Keys &&
                construct_signed_randao_reveal(rcvd_randao_share[slot]).isPresent() &&
                current_proposer_duty.isPresent())                
            {
                var randao_reveal := construct_signed_randao_reveal(rcvd_randao_share[slot]).safe_get();
                var duty := current_proposer_duty.safe_get();
                var is_valid_block: bool;
                is_valid_block := consensus_is_valid_block(block, duty, randao_reveal);
                if is_valid_block
                {                
                    update_block_slashing_db(block, duty.pubkey);
                    var block_signing_root := compute_block_signing_root(block);
                    var fork_version := bn.get_fork_version(slot);
                    var block_signature := rs.sign_block(block, fork_version, block_signing_root);
                    var block_share := SignedBeaconBlock(block, block_signature);
                    network.send_block_share(block_share, peers);    
                }                     
            }            
        }

        method listen_for_block_shares(block_share: SignedBeaconBlock)
        modifies this
        {
            var slot := block_share.message.slot;
            rcvd_block_share := rcvd_block_share[slot := getOrDefault(rcvd_block_share, slot, {}) + {block_share}];
            if construct_signed_block(rcvd_block_share[slot]).isPresent()
            {
                var complete_signed_block := construct_signed_block(rcvd_block_share[slot]).safe_get();  
                bn.submit_signed_block(complete_signed_block);  
            }
        }

        method update_block_slashing_db(block: BeaconBlock, pubkey: BLSPubkey)
        modifies this        
        {   
            var slashable := is_slashable_block(block, pubkey);

            if !slashable
            {
                var newDBBlock := SlashingDBBlock(pubkey, block.slot, hash_tree_root(block));
                var lastDBBlock := get_slashing_db_data_for_pubkey(pubkey);
                if lastDBBlock.isPresent() ==> lastDBBlock.safe_get().slot < block.slot
                {
                    block_slashing_db := block_slashing_db[pubkey := newDBBlock];
                }                
            }            
        }

        method is_slashable_block(
            block: BeaconBlock, 
            pubkey: BLSPubkey
        ) returns (b: bool)
        modifies this
        {            
            var dbBlock := get_slashing_db_data_for_pubkey(pubkey);
            if dbBlock.isPresent() 
            {
                var dbBlock_value := dbBlock.safe_get();
                if block.slot < dbBlock_value.slot
                {
                    return true;
                }
                    
                if block.slot == dbBlock_value.slot &&
                   hash_tree_root(block) != dbBlock_value.signing_root
                {
                    return true;
                }

                return false;
            }            
        }
        
        method get_slashing_db_data_for_pubkey(
            pubkey: BLSPubkey
        ) returns (dbBlock: Optional<SlashingDBBlock>)
        modifies this
        {   
            if pubkey in block_slashing_db.Keys
            {
                dbBlock := Some(block_slashing_db[pubkey]);
            }
            else 
            {
                dbBlock := None;
            }            
        }

        method is_valid_imported_blocks(
            block: BeaconBlock
        ) returns (b: bool)
        {
            // Check attestations
            var valid_attestations: bool;
            // Check proposer
            var valid_proposer: bool;
            // Check a parent
            var valid_parent: bool;
            // Check randao
            var valid_randao: bool;
            //
            b := valid_attestations && valid_proposer && valid_parent && valid_randao;
        }


        method listen_for_new_imported_blocks(
            block: BeaconBlock
        ) returns (s: Status)
        modifies this
        {
            var valid_block: bool := is_valid_imported_blocks(block);
            if valid_block && 
               (current_proposer_duty.isPresent() ==> block.slot >= current_proposer_duty.safe_get().slot)
               /* &&
               (!current_proposer_duty.isPresent() ==> 
                    (last_served_proposer_duty == None || 
                     (last_served_proposer_duty.isPresent() && block.slot > last_served_proposer_duty.safe_get().slot)))
                     */
            {
                future_decided_slots := future_decided_slots + {block.slot};
            }
            
            if current_proposer_duty.isPresent() && current_proposer_duty.safe_get().slot in future_decided_slots
            {
                var slot := current_proposer_duty.safe_get().slot;
                consensus_on_block.stop(slot);
                // Update past_decided_slots
                past_decided_slots := past_decided_slots + {slot};
                // last_served_proposer_duty := current_proposer_duty;
                check_for_next_queued_duty();
            }                                   
        }
    
    }    
}
