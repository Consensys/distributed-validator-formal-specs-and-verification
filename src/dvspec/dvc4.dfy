module Types 
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
    // type SignedBeaconBlock
    type {:extern "Root"} Root(==, 0)
    type {:extern "SyncCommitteeSignature"} SyncCommitteeSignature
    type {:extern "SyncCommitteeDuty"} SyncCommitteeDuty   
    type {:extern "Version"} Version    
    datatype Checkpoint = Checkpoint(
        epoch: Epoch,
        root: Root
    )

    type {:extern "Domain"} Domain(==)
    // type AttestationDuty 
    datatype AttestationData = AttestationData(
        slot: Slot,
        index: CommitteeIndex,
        // LMD GHOST vote
        beacon_block_root: Root,
        // FFG vote
        source: Checkpoint,
        target: Checkpoint
    )
    // type ProposerDuty
    datatype BeaconBlock = BeaconBlock(
        body: BeaconBlockBody
        // ... Other fields irrelevant to this spec
    )

    datatype BeaconBlockBody = BeaconBlockBody(
        attestations: seq<Attestation>,
        state_root: Root
        // ... Other fields irrelevant to this spec
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

    datatype AttestationDuty = AttestationDuty(
        pubkey: BLSPubkey,
        validator_index: ValidatorIndex,
        committee_index: CommitteeIndex,
        committee_length: nat,
        committees_at_slot: nat,
        validator_committee_index: ValidatorIndex,
        slot: Slot        
    )

    datatype ProposerDuty = ProposerDuty(
        pubkey: BLSPubkey,
        validator_index: ValidatorIndex,
        slot: Slot        
    )

    datatype SignedBeaconBlock = SignedBeaconBlock(
        message: BeaconBlock,
        signature: BLSSignature
    )

    type AttestationSlashingDB = set<SlashingDBAttestation>
    // class AttestationSlashingDB
    // {

    // }

    datatype BlockSlashingDB = BlockSlashingDB

    datatype  SlashingDBAttestation = SlashingDBAttestation(
        source_epoch: Epoch,
        target_epoch: Epoch,
        signing_root: Root
    )

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

    // datatype Outcome<T> =
    // | Success(value: T)
    // | Failure(error: string)
    // {
    //     predicate method IsFailure() {
    //         this.Failure?
    //     }
    //     function method PropagateFailure<U>(): Outcome<U>
    //         requires IsFailure()
    //     {
    //         Outcome.Failure(this.error) // this is Outcome<U>.Failure(...)
    //     }
    //     function method Extract(): T
    //         requires !IsFailure()
    //     {
    //         this.value
    //     }
    // }     

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
    }         

    function method getOrDefault<T1,T2>(M:map<T1,T2>, key:T1, default:T2): T2
    {
        if key in M.Keys then
            M[key]
        else
            default
    }     
}

module CoVNode_Implementation_Helpers
{
    import opened Types

    type AttestationSignatureShareDB = map<(AttestationData, seq<bool>), set<AttestationShare>>



    function method compute_start_slot_at_epoch(epoch: Epoch): Slot
    {
        epoch * SLOTS_PER_EPOCH
    }   

    datatype DomainTypes = 
        | DOMAIN_BEACON_ATTESTER


    // TDOO: What about the genesis_validator_root parameter?
    function method {:extern} compute_domain(
        domain_type: DomainTypes,
        fork_version: Version
    ): (domain: Domain)


    lemma {:axiom} compute_domain_properties()
    ensures forall d1, f1, d2, f2 :: compute_domain(d1, f2) == compute_domain(d2, f2) ==>
        && d1 == d2 
        && f1 == f2

    function method {:extern} compute_signing_root<T>(
        data: T,
        domain: Domain
    ): Root

    lemma {:axiom} compute_signing_root_properties<T>()
    ensures forall da1, do1, da2, do2 ::
        compute_signing_root<T>(da1, do1) == compute_signing_root<T>(da2, do2) ==>
            && da1 == da2 
            && do1 == do2

    // TODO: Fix Python code to match the following (Python code uses epoch)
    function method compute_attestation_signing_root(attestation_data: AttestationData, fork_version: Version): Root
    {
        var domain := compute_domain(DOMAIN_BEACON_ATTESTER, fork_version);
        compute_signing_root(attestation_data, domain)
    }



    predicate uniqueSeq<T(==)>(s: seq<T>)
    {
        forall i, j | 0 <= i < |s| && 0 <= j < |s| :: s[i] == s[j] ==> i == j
    }

    predicate {:extern} verify_bls_siganture<T>(
        data: T,
        signature: BLSSignature,
        pubkey: BLSPubkey
    )   

    function method {:extern} hash_tree_root<T>(data: T): Root 

    lemma {:axiom} hash_tree_root_properties<T>()
    ensures forall d1: T, d2: T :: hash_tree_root(d1) == hash_tree_root(d2) ==> d1 == d2
}

module CoVNode_Externs
{
    import opened Types
    import opened CoVNode_Implementation_Helpers  

    datatype ConsensuCommand = 
        | Start(id: Slot)
        | Stop(id: Slot)       

    class Consensus {
        var consensus_commands_sent: seq<ConsensuCommand>

        constructor()
        {
            consensus_commands_sent := [];
        }

        method {:extern} start(
            id: Slot
        )
        ensures consensus_commands_sent == old(consensus_commands_sent) + [Start(id)]

        method {:extern} stop(
            id: Slot
        )
        ensures consensus_commands_sent == old(consensus_commands_sent) + [Stop(id)]        
    }     

    class Network  
    {
        ghost const att_shares_sent: seq<AttestationShare>;
        // ghost var atts_sent: seq<Attestation>;

        constructor()
        {
            att_shares_sent := [];
        }

        method {:extern} send_att_share(att_share: AttestationShare)
        ensures att_shares_sent == old(att_shares_sent)  + [att_share]

        // function setToSeq<T(!new)>(s: set<T>): (r: seq<T>)
        // ensures forall e :: e in s <==> e in r

        // ghost method send_atts(atts: set<Attestation>)
        // ensures atts_sent == old(atts_sent) + setToSeq(atts)
    }

    class BeaconNode
    {
        ghost var state_roots_of_imported_blocks: set<Root>;
        ghost const attestations_submitted: seq<Attestation>; 

        constructor()
        {
            attestations_submitted := [];
            state_roots_of_imported_blocks := {};
        }

        method {:extern} get_fork_version(s: Slot) returns (v: Version)

        method {:extern} submit_attestation(attestation: Attestation)
        ensures attestations_submitted == old(attestations_submitted) + [attestation]

        // https://ethereum.github.io/beacon-APIs/?urls.primaryName=v1#/Beacon/getEpochCommittees
        method {:extern} get_epoch_committees(
            state_id: Root,
            index: CommitteeIndex
        ) returns (s: Status, sv: seq<ValidatorIndex>)
        ensures state_id in state_roots_of_imported_blocks <==> s.Success?
        ensures uniqueSeq(sv)  

        // https://ethereum.github.io/beacon-APIs/#/Beacon/getStateValidator
        method {:extern} get_validator_index(
            state_id: Root,
            validator_id: BLSPubkey
        ) returns (s: Status, vi: Optional<ValidatorIndex>)
        ensures state_id in state_roots_of_imported_blocks <==> s.Success?
    }

    class RemoteSigner
    {
        const pubkey: BLSPubkey;

        constructor(
            pubkey: BLSPubkey
        )
        {
            this.pubkey := pubkey;
        }

        method {:extern} sign_attestation(
            attestation_data: AttestationData, 
            fork_version: Version, 
            signing_root: Root           
        ) returns (s: BLSSignature)

    }
}


// abstract module X 
// {
//     import opened Types
//     // import opened CoVNode_Externs
//     import opened CoVNode_Implementation_Helpers    
//     import opened CoVNode_Implementation`PublicInterface

//     method test(x: CoVNode, bn: CoVNode_Externs.BeaconNode)
//     modifies x
//     modifies x.bn
//     {
//         var a: AttestationDuty :| true;
//         // x.current_attesation_duty := None;
//         // x.serve_attestation_duty(a);
//         x.bn.state_roots_of_imported_blocks := {};
        
//         // x.check_for_next_queued_duty();
//     }
// }

abstract module CoVNode_Implementation
{
    import opened Types
    import opened CoVNode_Implementation_Helpers
    import opened CoVNode_Externs: CoVNode_Externs

    export PublicInterface
        reveals CoVNode
        provides
                CoVNode.serve_attestation_duty, 
                CoVNode.att_consensus_decided, 
                CoVNode.listen_for_attestation_duty_shares,
                CoVNode.listen_for_new_imported_blocks,
                CoVNode.resend_attestation_share,
                CoVNode.bn
        provides Types, CoVNode_Implementation_Helpers, CoVNode_Externs

    class CoVNode {

        var current_attesation_duty: Optional<AttestationDuty>;
        var attestation_duties_queue: seq<AttestationDuty>;
        // var pubkey: BLSPubkey;
        var attestation_slashing_db: AttestationSlashingDB;
        var attestation_shares_db: AttestationSignatureShareDB;
        var attestation_share_to_broadcast: Optional<AttestationShare>
        var construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>;
        // TODO: Note difference with spec.py
        var dv_pubkey: BLSPubkey;
        var future_att_consensus_instances_already_decided: set<Slot>

        var att_consensus: Consensus;
        const network : Network
        const bn: BeaconNode;
        const rs: RemoteSigner;

        constructor(
            pubkey: BLSPubkey, 
            dv_pubkey: BLSPubkey,
            att_consensus: Consensus, 
            network: Network,
            bn: BeaconNode,
            rs: RemoteSigner,
            construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>)
        {
            current_attesation_duty := None;
            attestation_share_to_broadcast := None;
            attestation_shares_db := map[];

            // this.pubkey := pubkey;
            this.att_consensus := att_consensus;
            this.network := network;
            this.rs := rs;
            this.bn := bn;
            this.construct_signed_attestation_signature := construct_signed_attestation_signature;
            this.dv_pubkey := dv_pubkey;
            this.future_att_consensus_instances_already_decided := {};
        }

        method serve_attestation_duty(
            attestation_duty: AttestationDuty
        )
        modifies this
        {
            attestation_duties_queue := attestation_duties_queue + [attestation_duty];
            check_for_next_queued_duty();
        }

        method check_for_next_queued_duty()
        modifies this
        decreases attestation_duties_queue
        {
            if attestation_duties_queue != []
            {
                if attestation_duties_queue[0].slot in future_att_consensus_instances_already_decided
                {
                    attestation_duties_queue := attestation_duties_queue[1..];
                    check_for_next_queued_duty();
                }
                else
                {
                    start_next_duty(attestation_duties_queue[0]);
                }
            }
        }

        method start_next_duty(attestation_duty: AttestationDuty)
        modifies this
        {
            attestation_shares_db := map[];
            attestation_share_to_broadcast := None;
            current_attesation_duty := Some(attestation_duty);
            att_consensus.start(attestation_duty.slot);            
        }        

        method update_attestation_slashing_db(attestation_data: AttestationData, attestation_duty_pubkey: BLSPubkey)
        modifies this       
        {
            // assert not is_slashable_attestation_data(attestation_slashing_db, attestation_data, pubkey)
            // TODO: Is the following required given that each co-validator only handles one pubkey?
            // slashing_db_data = get_slashing_db_data_for_pubkey(attestation_slashing_db, pubkey)
            var slashing_db_attestation := SlashingDBAttestation(
                                                source_epoch := attestation_data.source.epoch,
                                                target_epoch := attestation_data.target.epoch,
                                                signing_root := hash_tree_root(attestation_data));
            attestation_slashing_db := attestation_slashing_db + {slashing_db_attestation};
        }

        method att_consensus_decided(
            decided_attestation_data: AttestationData
        ) returns (r: Status)
        modifies this
        {
            var local_current_attestation_duty :- current_attesation_duty.get();
            update_attestation_slashing_db(decided_attestation_data, local_current_attestation_duty.pubkey);
 
            var fork_version := bn.get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
            var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
            var attestation_signature_share := rs.sign_attestation(decided_attestation_data, fork_version, attestation_signing_root);
            // TODO: What is attestation_signature_share.aggregation_bits?
            var attestation_with_signature_share := AttestationShare(
                aggregation_bits := get_aggregation_bits(local_current_attestation_duty.validator_index),
                data := decided_attestation_data, 
                signature :=attestation_signature_share
            ); 

            attestation_share_to_broadcast := Some(attestation_with_signature_share);
            network.send_att_share(attestation_with_signature_share);           
        }

        function method get_aggregation_bits(
            index: nat
        ): (s: seq<bool>)
        ensures |s| == index
        ensures forall i | 0 <= i < |s| :: if i == index - 1 then s[i] else !s[i]
        {
            seq(index, i => if i + 1 == index then true else false)
        }        

        method listen_for_attestation_duty_shares(
            attestation_share: AttestationShare
        )
        modifies this
        {
            // TODO: Decide 
            // 1. whether to add att shares to db only if already served attestation duty
            // 2. when to wipe out the db
            var k := (attestation_share.data, attestation_share.aggregation_bits);
            attestation_shares_db := 
                attestation_shares_db[k := 
                                        getOrDefault(attestation_shares_db, k, {}) + 
                                        {attestation_share}
                                    ];
                        
            if construct_signed_attestation_signature(attestation_shares_db[k]).isPresent()
            {
                var aggregated_attestation := 
                        Attestation(
                            aggregation_bits := attestation_share.aggregation_bits,
                            data := attestation_share.data,
                            signature := construct_signed_attestation_signature(attestation_shares_db[k]).safe_get()
                        );
                bn.submit_attestation(aggregated_attestation); 
            }  
        }

        method listen_for_new_imported_blocks(
            block: BeaconBlock
        ) returns (s: Status)
        modifies this
        {
            var valIndex :- bn.get_validator_index(block.body.state_root, dv_pubkey);
            var i := 0;

            while i < |block.body.attestations|
            // for i := 0 to |block.body.attestations|
            {
                var a := block.body.attestations[i];
                var committee :- bn.get_epoch_committees(block.body.state_root, a.data.index);
                
                if
                && a in block.body.attestations
                // && a.data.slot == process.attestation_duty.slot 
                // && a.data.index == process.attestation_duty.committee_index
                && valIndex.Some?
                && valIndex.v in committee
                && var i:nat :| i < |committee| && committee[i] == valIndex.v;
                && i < |a.aggregation_bits|
                && a.aggregation_bits[i]
                && (current_attesation_duty.isPresent() ==> a.data.slot >= current_attesation_duty.safe_get().slot)
                {
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided + {a.data.slot};
                }

                i := i + 1;
            }


            if current_attesation_duty.isPresent() && current_attesation_duty.safe_get().slot in future_att_consensus_instances_already_decided
            {
                att_consensus.stop(current_attesation_duty.safe_get().slot);
                check_for_next_queued_duty();
            }                                   
        }

        method resend_attestation_share(
        )
        modifies this
        {
            if attestation_share_to_broadcast.isPresent()
            {
                network.send_att_share(attestation_share_to_broadcast.safe_get());
            }
        }        
    }    
}

