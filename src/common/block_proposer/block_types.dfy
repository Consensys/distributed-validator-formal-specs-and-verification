module Block_Types 
{
    type ValidatorIndex = nat
    type Epoch = nat 
    type Slot = nat
    const SLOTS_PER_EPOCH := 32
    type {:extern "CommitteeIndex"} CommitteeIndex(!new, 0)
    // type Attestation 
    type {:extern "BLSSignature"} BLSSignature(==, !new, 0)
    type {:extern "BLSPubkey"} BLSPubkey(==, !new, 0)
    type {:extern "Bytes32"} Bytes32(0)
    
    type {:extern "Root"} Root(==, 0, !new)
    type {:extern "SyncCommitteeSignature"} SyncCommitteeSignature
    type {:extern "SyncCommitteeDuty"} SyncCommitteeDuty   
    type {:extern "Version"} Version(!new)   
    datatype Checkpoint = Checkpoint(
        epoch: Epoch,
        root: Root
    )

    type {:extern "Domain"} Domain(==)

    datatype AttestationDuty = AttestationDuty(
        pubkey: BLSPubkey,
        validator_index: ValidatorIndex,
        committee_index: CommitteeIndex,
        committee_length: nat,
        committees_at_slot: nat,
        validator_committee_index: ValidatorIndex,
        slot: Slot        
    )

    datatype AttestationData = AttestationData(
        slot: Slot,
        index: CommitteeIndex,
        // LMD GHOST vote
        beacon_block_root: Root,
        // FFG vote
        source: Checkpoint,
        target: Checkpoint
    )

    datatype Attestation = Attestation(
        aggregation_bits: seq<bool>,
        data: AttestationData,
        signature: BLSSignature
    )

    datatype AttestationShare = AttestationShare(
        aggregation_bits: seq<bool>,
        data: AttestationData,
        signature: BLSSignature
    )

    datatype  SlashingDBAttestation = SlashingDBAttestation(
        source_epoch: Epoch,
        target_epoch: Epoch,
        signing_root: Root
    )    

    type AttestationSlashingDB = set<SlashingDBAttestation>
         
    type AttestationSignatureShareDB = map<(AttestationData, seq<bool>), set<AttestationShare>>   

    datatype RandaoShare = RandaoShare(
        proposer_duty: ProposerDuty,
        slot: Slot,
        signing_root: Root,
        signature: BLSSignature
    )

    datatype BeaconBlockBody = BeaconBlockBody(
        attestations: seq<Attestation>,        
        state_root: Root,
        randao_reveal: BLSSignature
        // ... Other fields irrelevant to this spec
    )

    datatype ProposerDuty = ProposerDuty(
        pubkey: BLSPubkey,
        validator_index: ValidatorIndex,
        slot: Slot        
    )

    datatype BeaconBlock = BeaconBlock(
        slot: Slot,
        proposer_index: ValidatorIndex,
        parent_root: Root,
        state_root: Root,
        body: BeaconBlockBody
        // ... Other fields irrelevant to this spec
    )

    datatype SignedBeaconBlock = SignedBeaconBlock(
        block: BeaconBlock,
        signature: BLSSignature
    )
 
    datatype SlashingDBBlock = SlashingDBBlock(        
        slot: Slot,
        signing_root: Root 
    )
    
    // The block slashing database is only with one pubkey.
    // Not use SlashingDBData explicitly since this work focuses only on blocks.
    type BlockSlashingDB = set<SlashingDBBlock>
         
    type BlockSignatureShareDB = map<(BeaconBlock, seq<bool>), set<SignedBeaconBlock>>   

    datatype Status =
    | Success
    | Failure(error: string)
    {
        predicate method IsFailure() { this.Failure?  }

        function method PropagateFailure(): Status
            requires IsFailure()
        {
            Status.Failure(this.error)
        }
    }   

    type imaptotal<!T1(!new), T2> = x: imap<T1,T2> | forall e: T1 :: e in x.Keys witness *
    type iseq<T> = imaptotal<nat, T>

    datatype ConsensusCommand = 
        | StartConsensusOnBlock(id: Slot)
        | StopConsensusOnBlock(id: Slot)    
              

    datatype Optional<T(0)> = Some(v: T) | None
    {
        predicate method isPresent()
        {
            this.Some?
        }

        method get() returns (o: Status, v: T)
        ensures isPresent() ==> o.Success? && v == safe_get()
        ensures !isPresent() ==> o.Failure?
        {
            if isPresent()
            {
                return Success, this.v;
            }
            else {
                var dummyVal;
                return Failure(""), dummyVal;
            }
        }

        function method safe_get(): T
        requires isPresent()
        {
            this.v
        } 

        function toSet(): set<T> 
        {
            if isPresent() then
                {this.v}
            else 
                {}
        }  

        static function toOptional(s: set<T>): (o: Optional<T>)
        requires |s| <= 1
        ensures o.isPresent() ==> s == {o.safe_get()}
        {
            if s == {} then
                None 
            else
                var e :| e in s;
                assert |s - {e}| == 0;
                Some(e)
        } 
    }        

    datatype MessaageWithRecipient<M> = MessaageWithRecipient(
        message: M,
        receipient: BLSPubkey
    ) 
    
    // Add types for the DVT protocol on blocks
    datatype DomainTypes = 
        | DOMAIN_BEACON_ATTESTER
        | DOMAIN_RANDAO
        | DOMAIN_BEACON_PROPOSER
     
    // // Add a field Slot into datatype BLSSignature
    // datatype BLSSignature = BLSSignature(
    //     proposer_duty: ProposerDuty,
    //     epoch: Epoch,
    //     slot: Slot,
    //     root: Root,
    //     signature: BLSSignature
    // )

    datatype Event = 
        | ServeProposerDuty(proposer_duty: ProposerDuty)
        | BlockConsensusDecided(id: Slot, block: BeaconBlock)
        | ReceiveRandaoShare(randao_share: RandaoShare)
        | ReceiveSignedBeaconBlock(block_share: SignedBeaconBlock)
        | ImportedNewBlock(block: BeaconBlock)       
        | ResendRandaoRevealSignatureShare
        | ResendBlockShare
        | NoEvent      

    datatype BlockConsensusValidityCheckState = BlockConsensusValidityCheckState(
        proposer_duty: ProposerDuty,
        complete_signed_randao_reveal: BLSSignature,
        validityPredicate: BeaconBlock -> bool
    )


 
}

