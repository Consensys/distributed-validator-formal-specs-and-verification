include "../../common/commons.dfy"
include "../../common/commons.dfy"
include "../../common/block_proposer/block_signing_functions.dfy"

module Block_DVC_Externs
{
    import opened Types
    import opened CommonFunctions
    

    trait 
    // See https://github.com/dafny-lang/dafny/issues/1588 for why {:termination false} is needed
    {:termination false} 
    {:autocontracts} ConsensusValidityCheck<T>
    {
        const slashing_db: SlashingDB

        method is_valid(data: T) returns (validity: bool)
    }      

    trait {:autocontracts} Consensus<T(!new, ==)>
    {
        ghost var consensus_instances_started: map<Slot, ConsensusValidityCheck<T>>

        method start(
            id: Slot,
            validityPredicate: ConsensusValidityCheck<T>
        )
        ensures consensus_instances_started == old(consensus_instances_started)[id := validityPredicate]

        method stop_multiple(
            ids: set<Slot>
        )
        ensures consensus_instances_started == old(consensus_instances_started) - ids

        method get_active_instances() returns (active_instances: set<Slot>)
        ensures active_instances == consensus_instances_started.Keys 
        ensures unchanged(`consensus_instances_started) 

    }    

    trait {:autocontracts} Network  
    {
        ghost var sent_block_shares: seq<set<MessaageWithRecipient<SignedBeaconBlock>>>;
        ghost var sent_randao_shares: seq<set<MessaageWithRecipient<RandaoShare>>>;

        method send_block_share(block_share: SignedBeaconBlock, receipients: set<BLSPubkey>)
        ensures sent_block_shares == old(sent_block_shares)  + [wrapMessageWithRecipients(block_share, receipients)]  
        ensures unchanged(`sent_randao_shares)

        method send_block_shares(block_shares: set<SignedBeaconBlock>, receipients: set<BLSPubkey>)
        ensures var setWithRecipient := set block_share | block_share in block_shares :: wrapMessageWithRecipients(block_share, receipients);
                sent_block_shares == old(sent_block_shares)  + [setUnion(setWithRecipient)]
        ensures unchanged(`sent_randao_shares)        

        method send_randao_share(randao_share: RandaoShare, receipients: set<BLSPubkey>)
        ensures sent_randao_shares == old(sent_randao_shares)  + [wrapMessageWithRecipients(randao_share, receipients)]
        ensures unchanged(`sent_block_shares)

        method send_randao_shares(randao_shares: set<RandaoShare>, receipients: set<BLSPubkey>)
        ensures var setWithRecipient := set randao_share | randao_share in randao_shares :: wrapMessageWithRecipients(randao_share, receipients);
                sent_randao_shares == old(sent_randao_shares)  + [setUnion(setWithRecipient)]
        ensures unchanged(`sent_block_shares)        
    }

    trait {:autocontracts} BeaconNode
    {        
        ghost var submitted_signed_block: seq<SignedBeaconBlock>; 

        method {:extern} get_fork_version(s: Slot) returns (v: Version)
        ensures unchanged(`submitted_signed_block)

        method {:extern} submit_signed_block(block: SignedBeaconBlock)
        ensures submitted_signed_block == old(submitted_signed_block) + [block]

        method {:extern} get_block(randao_reveal: BLSSignature) returns (b: BeaconBlock)
        ensures unchanged(`submitted_signed_block)        
 
    }

    trait {:autocontracts} RemoteSigner
    {
        const pubkey: BLSPubkey;

        // eth_node_interface.py --> rs_sign_block
        method sign_block(
            block: BeaconBlock,
            fork_version: Version, 
            signing_root: Root           
        ) returns (s: BLSSignature)
        requires signing_root == compute_block_signing_root(block)

        // eth_node_interface.py --> rs_sign_randao_reveal
        // Check the pre-condition that is based on the first slot of an epoch.
        method {:extern} sign_randao_reveal(
            epoch: Epoch,
            fork_version: Version, 
            signing_root: Root           
        ) returns (s: BLSSignature)
        requires signing_root == compute_randao_reveal_signing_root(epoch * SLOTS_PER_EPOCH)
    }
    
    // NOTE: All methods in this trait MUST be implemented thread-safe.
    trait {:autocontracts} SlashingDB
    {
        ghost var attestations: imaptotal<BLSPubkey, set<SlashingDBAttestation>>;
        ghost var proposals: imaptotal<BLSPubkey, set<SlashingDBBlock>>

        method add_attestation(attestation: SlashingDBAttestation, pubkey: BLSPubkey)
        ensures attestations == old(attestations)[pubkey := old(attestations)[pubkey] + {attestation}]
        ensures unchanged(`proposals)

        method get_attestations(pubkey: BLSPubkey) returns (attestations: set<SlashingDBAttestation>)
        ensures attestations == this.attestations[pubkey]
        ensures unchanged(`attestations)
        ensures unchanged(`proposals)

        method add_proposal(block: SlashingDBBlock, pubkey: BLSPubkey)
        ensures proposals == old(proposals)[pubkey := old(proposals)[pubkey] + {block}]
        ensures unchanged(`attestations)

        method get_proposals(pubkey: BLSPubkey) returns (proposals: set<SlashingDBBlock>)
        ensures proposals == this.proposals[pubkey]
        ensures unchanged(`attestations)
        ensures unchanged(`proposals)        
    }     
}

