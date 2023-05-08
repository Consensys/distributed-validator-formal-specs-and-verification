include "../common/commons.dfy"

module DVC_Externs
{
    import opened Types
    import opened CommonFunctions

    trait 
    // See https://github.com/dafny-lang/dafny/issues/1588 for why {:termination false} is needed
    {:termination false} 
    {:autocontracts} ConsensusValidityCheck<T, SlashingDBType(==)>
    {
        const slashing_db: SlashingDB<SlashingDBType>

        method is_valid(data: T) returns (validity: bool)
    }    

    trait {:autocontracts} Consensus<T(!new, ==), SlashingDBType(!new, ==)>
    {
        ghost var consensus_instances_started: map<Slot, ConsensusValidityCheck<T, SlashingDBType>>

        method start(
            id: Slot,
            validityPredicate: ConsensusValidityCheck<T, SlashingDBType>
        ) returns (s: Status)
        ensures s.Success? <==> id !in old(consensus_instances_started.Keys)
        ensures s.Success? ==> consensus_instances_started == old(consensus_instances_started)[id := validityPredicate]
        ensures s.Failure? ==> unchanged(`consensus_instances_started)  

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
        ghost var att_shares_sent: seq<set<MessaageWithRecipient<AttestationShare>>>;

        method send_att_share(att_share: AttestationShare, receipients: set<BLSPubkey>)
        ensures att_shares_sent == old(att_shares_sent)  + [addRecepientsToMessage(att_share, receipients)]

        method send_att_shares(att_shares: set<AttestationShare>, receipients: set<BLSPubkey>)
        ensures     var setWithRecipient := set att_share | att_share in att_shares :: addRecepientsToMessage(att_share, receipients);
                    att_shares_sent == old(att_shares_sent)  + [setUnion(setWithRecipient)]
        ensures unchanged(`att_shares_sent)

        ghost var sent_block_shares: seq<set<MessaageWithRecipient<SignedBeaconBlock>>>;
        ghost var sent_randao_shares: seq<set<MessaageWithRecipient<RandaoShare>>>;

        method send_block_share(block_share: SignedBeaconBlock, receipients: set<BLSPubkey>)
        ensures sent_block_shares == old(sent_block_shares)  + [addRecepientsToMessage(block_share, receipients)]  
        ensures unchanged(`sent_randao_shares)

        method send_block_shares(block_shares: set<SignedBeaconBlock>, receipients: set<BLSPubkey>)
        ensures var setWithRecipient := set block_share | block_share in block_shares :: addRecepientsToMessage(block_share, receipients);
                sent_block_shares == old(sent_block_shares)  + [setUnion(setWithRecipient)]
        ensures unchanged(`sent_randao_shares)        

        method send_randao_share(randao_share: RandaoShare, receipients: set<BLSPubkey>)
        ensures sent_randao_shares == old(sent_randao_shares)  + [addRecepientsToMessage(randao_share, receipients)]
        ensures unchanged(`sent_block_shares)

        method send_randao_shares(randao_shares: set<RandaoShare>, receipients: set<BLSPubkey>)
        ensures var setWithRecipient := set randao_share | randao_share in randao_shares :: addRecepientsToMessage(randao_share, receipients);
                sent_randao_shares == old(sent_randao_shares)  + [setUnion(setWithRecipient)]
        ensures unchanged(`sent_block_shares)      

    }

    trait {:autocontracts} BeaconNode<T(!new, ==)>
    {
        ghost var state_roots_of_imported_blocks: set<Root>;
        ghost var data_submitted: seq<T>; 

        method get_fork_version(s: Slot) returns (v: Version)
        ensures unchanged(`state_roots_of_imported_blocks)
        ensures unchanged(`data_submitted)

        method submit_data(data: T)
        ensures data_submitted == old(data_submitted) + [data]
        ensures unchanged(`state_roots_of_imported_blocks)

        // https://ethereum.github.io/beacon-APIs/?urls.primaryName=v1#/Beacon/getEpochCommittees
        method get_epoch_committees(
            state_id: Root,
            index: CommitteeIndex
        ) returns (s: Status, sv: seq<ValidatorIndex>)
        ensures unchanged(`state_roots_of_imported_blocks)
        ensures unchanged(`data_submitted)        
        ensures state_id in state_roots_of_imported_blocks <==> s.Success?
        ensures uniqueSeq(sv)  

        // https://ethereum.github.io/beacon-APIs/#/Beacon/getStateValidator
        method get_validator_index(
            state_id: Root,
            validator_id: BLSPubkey
        ) returns (s: Status, vi: Optional<ValidatorIndex>)
        ensures unchanged(`state_roots_of_imported_blocks)
        ensures unchanged(`data_submitted)        
        ensures state_id in state_roots_of_imported_blocks <==> s.Success?
    }

    trait {:autocontracts} RemoteSigner
    {
        const pubkey: BLSPubkey;

        method sign_attestation(
            attestation_data: AttestationData, 
            fork_version: Version, 
            signing_root: Root           
        ) returns (s: BLSSignature)
        requires signing_root == compute_attestation_signing_root(attestation_data, fork_version)

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
    trait {:autocontracts} SlashingDB<SlashingDBType(==)>
    {
        ghost var slashingDBRecords: imaptotal<BLSPubkey, set<SlashingDBType>>;

        method add_record(new_record: SlashingDBType, pubkey: BLSPubkey)
        ensures slashingDBRecords == old(slashingDBRecords)[pubkey := old(slashingDBRecords)[pubkey] + {new_record}]

        method get_records(pubkey: BLSPubkey) returns (records: set<SlashingDBType>)
        ensures records == this.slashingDBRecords[pubkey]
    }   

    // trait {:autocontracts} BlockSlashingDB
    // {
    //     ghost var blocks: imaptotal<BLSPubkey, set<SlashingDBBlock>>

    //     method add_proposal(block: SlashingDBBlock, pubkey: BLSPubkey)
    //     ensures blocks == old(blocks)[pubkey := old(blocks)[pubkey] + {block}]

    //     method get_proposals(pubkey: BLSPubkey) returns (blocks: set<SlashingDBBlock>)
    //     ensures blocks == this.blocks[pubkey]
    // }    
}

