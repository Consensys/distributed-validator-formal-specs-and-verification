module Types 
{
    type ValidatorIndex = nat
    type Epoch = nat 
    type Slot = nat
    const SLOTS_PER_EPOCH := 32
    type {:extern "CommitteeIndex"} CommitteeIndex(!new, 0, ==)
    // type Attestation 
    type {:extern "BLSSignature"} BLSSignature(==, !new, 0)
    type {:extern "BLSPubkey"} BLSPubkey(==, !new, 0)
    type {:extern "Bytes32"} Bytes32(0)
    // type SignedBeaconBlock
    type {:extern "Root"} Root(==, 0, !new)
    type {:extern "SyncCommitteeSignature"} SyncCommitteeSignature
    type {:extern "SyncCommitteeDuty"} SyncCommitteeDuty   
    type {:extern "Version"} Version(!new)   
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

    datatype BlockSlashingDB = BlockSlashingDB
    type SlashingDBBlock(==, !new)

    datatype  SlashingDBAttestation = SlashingDBAttestation(
        source_epoch: Epoch,
        target_epoch: Epoch,
        signing_root: Optional<Root>
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

    datatype Event = 
    | ServeAttstationDuty(attestation_duty: AttestationDuty)
    | AttConsensusDecided(id: Slot, decided_attestation_data: AttestationData)
    | ReceviedAttesttionShare(attestation_share: AttestationShare)
    | ImportedNewBlock(block: BeaconBlock)
    | ResendAttestationShares
    | NoEvent    

    type imaptotal<!T1(!new), T2> = x: imap<T1,T2> | forall e: T1 :: e in x.Keys witness *
    type iseq<T> = imaptotal<nat, T>

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
}

module CommonFunctions{
    import opened Types

    function method getOrDefault<T1,T2>(M:map<T1,T2>, key:T1, default:T2): T2
    {
        if key in M.Keys then
            M[key]
        else
            default
    }      

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
    
    lemma {:axiom} exists_att_data_for_every_slashingDBattestaion()
    ensures forall r: SlashingDBAttestation :: 
                exists data: AttestationData :: 
                    r.signing_root == Some(hash_tree_root(data))

    lemma {:axiom} exists_att_data_for_given_slashingDBattestaion(r: SlashingDBAttestation)
    ensures exists data: AttestationData :: r.signing_root == Some(hash_tree_root(data))

    function getMessagesFromMessagesWithRecipient<M>(mswr: set<MessaageWithRecipient<M>>): set<M>
    {
        set mwr | mwr in mswr :: mwr.message
    }

    function addReceipientToMessages<M>(sm: set<M>, r: BLSPubkey): set<MessaageWithRecipient<M>>
    {
        set m | m in sm :: MessaageWithRecipient(
            message :=  m,
            receipient := r
        )
    }

    function addRecepientsToMessage<M>(m: M, receipients: set<BLSPubkey>): set<MessaageWithRecipient<M>>
    {
        set r | r in receipients :: MessaageWithRecipient(message := m, receipient := r)
    }

    function setUnion<T>(sets:set<set<T>>):set<T>
    {
        set s, e | s in sets && e in s :: e
    } 

    function seqToSet<T>(s: seq<T>): (r: set<T>)
    {
        set e | e in s
    }

    lemma minOfSetOfIntExists(s: set<int>)
    requires s != {}
    ensures exists min :: 
                        && min in s 
                        && forall e | e in s :: min <= e 
    {
        if |s| == 1 {
            var e :| e in s;
            assert |s - {e}| == 0;
        } 
        else
        {
            var e :| e in s;
            var sMinusE := s - {e};
            assert |s| > 1;
            assert s == sMinusE + {e};
            assert |sMinusE| > 0;
            minOfSetOfIntExists(sMinusE);
            var mMinusE :| mMinusE in sMinusE && forall e' | e' in sMinusE :: e' >= mMinusE;
        }    
    }  

    lemma maxOfSetOfIntExists(s: set<int>)
    requires s != {}
    ensures exists min :: 
                        && min in s 
                        && forall e | e in s :: min >= e 
    {
        if |s| == 1 {
            var e :| e in s;
            assert |s - {e}| == 0;
        } 
        else
        {
            var e :| e in s;
            var sMinusE := s - {e};
            assert |s| > 1;
            assert s == sMinusE + {e};
            assert |sMinusE| > 0;
            maxOfSetOfIntExists(sMinusE);
            var mMinusE :| mMinusE in sMinusE && forall e' | e' in sMinusE :: e' <= mMinusE;
        }    
    }    

    function method {:opaque} minSet(s: set<int>): (min: int)
    requires s != {}
    ensures min in s 
    ensures forall e | e in s :: min <= e 
    {
        minOfSetOfIntExists(s);
        var e :| e in s && forall e' | e' in s :: e' >= e;
        e
    }

    function method {:opaque} maxSet(s: set<int>): (max: int)
    requires s != {}
    ensures max in s 
    ensures forall e | e in s :: max >= e 
    {
        maxOfSetOfIntExists(s);
        var e :| e in s && forall e' | e' in s :: e' <= e;
        e
    }   

    function method get_target_epochs(att_slashing_db: set<SlashingDBAttestation>): (target_epochs: set<nat>)
    requires att_slashing_db != {}
    ensures target_epochs != {}
    {
        var target_epochs := set attn | attn in att_slashing_db :: attn.target_epoch;
        assert var e :| e in att_slashing_db; e.target_epoch in target_epochs;
        target_epochs
    }

    function method get_source_epochs(att_slashing_db: set<SlashingDBAttestation>): (source_epochs: set<nat>)
    requires att_slashing_db != {}
    ensures source_epochs != {}
    {
        var source_epochs := set attn | attn in att_slashing_db :: attn.source_epoch;
        assert var e :| e in att_slashing_db; e.source_epoch in source_epochs;
        source_epochs
    }    

    predicate method is_slashable_attestation_pair(data_1: SlashingDBAttestation, data_2: SlashingDBAttestation)
    {
        // Double vote - over approximated check compared to the 
        // code in the Eth reference implementation as
        // here we do not have all the fields of AttestationData
        || (data_1.target_epoch == data_2.target_epoch) 
        // Surround vote
        || (data_1.source_epoch < data_2.source_epoch && data_2.target_epoch < data_1.target_epoch)        
    }

    predicate is_slashable_attestation_data(att_slashing_db: set<SlashingDBAttestation>, attestation_data: AttestationData)
    {
        // Check for EIP-3076 conditions:
        // https://eips.ethereum.org/EIPS/eip-3076#conditions
        if att_slashing_db != {} then
            var min_target := minSet(get_target_epochs(att_slashing_db));
            var min_source := minSet(get_source_epochs(att_slashing_db));
            if attestation_data.target.epoch <= min_target then
                true 
            else if attestation_data.source.epoch < min_source then
                true
            else 
                var slashing_db_att_for_att_data := 
                    SlashingDBAttestation(
                        source_epoch := attestation_data.source.epoch,
                        target_epoch := attestation_data.target.epoch,
                        signing_root := None
                    );            
                exists past_attn | past_attn in att_slashing_db ::
                        || is_slashable_attestation_pair(past_attn, slashing_db_att_for_att_data)
                        || is_slashable_attestation_pair(slashing_db_att_for_att_data, past_attn)
        else
            false        
    } by method 
    {
        // Check for EIP-3076 conditions:
        // https://eips.ethereum.org/EIPS/eip-3076#conditions
        if att_slashing_db != {} 
        {
            var min_target := minSet(get_target_epochs(att_slashing_db));
            var min_source := minSet(get_source_epochs(att_slashing_db));
            if attestation_data.target.epoch <= min_target
            {
                assert is_slashable_attestation_data(att_slashing_db, attestation_data);
                return true;
            }
            else if attestation_data.source.epoch < min_source
            {
                assert is_slashable_attestation_data(att_slashing_db, attestation_data);
                return true;
            }
            else 
            {
                var attns_to_check := att_slashing_db;
                var slashing_db_att_for_att_data := 
                    SlashingDBAttestation(
                        source_epoch := attestation_data.source.epoch,
                        target_epoch := attestation_data.target.epoch,
                        signing_root := None
                    );
                while attns_to_check != {}
                invariant var checked := att_slashing_db - attns_to_check;
                        forall a | a in checked :: 
                            && !is_slashable_attestation_pair(a, slashing_db_att_for_att_data)
                            && !is_slashable_attestation_pair(slashing_db_att_for_att_data, a)
                {
                        var past_attn :| past_attn in attns_to_check;
                        if || is_slashable_attestation_pair(past_attn, slashing_db_att_for_att_data)
                           || is_slashable_attestation_pair(slashing_db_att_for_att_data, past_attn)
                        {
                            assert is_slashable_attestation_data(att_slashing_db, attestation_data);
                            return true;
                        }

                        attns_to_check := attns_to_check - {past_attn};
                }
                assert !is_slashable_attestation_data(att_slashing_db, attestation_data);
                return false;
            }

        }
        else
        {
            assert !is_slashable_attestation_data(att_slashing_db, attestation_data);
            return false;
        }
    } 

    predicate method consensus_is_valid_attestation_data(
        slashing_db: set<SlashingDBAttestation>,
        attestation_data: AttestationData, 
        attestation_duty: AttestationDuty
    )
    {
        && attestation_data.slot == attestation_duty.slot
        && attestation_data.index == attestation_duty.committee_index
        && !is_slashable_attestation_data(slashing_db, attestation_data)  
        && attestation_data.source.epoch < attestation_data.target.epoch 
    }      

    // Given an attestation, returns its slot
    function method get_slot_from_att(att: Attestation): Slot
    {
        att.data.slot
    }

    // Given an attestation data d and a slashing DB attestation dbAttRecord, 
    // check whether dbAttRecord is based on d.
    predicate method is_SlashingDBAtt_for_given_att_data(
        dbAttRecord: SlashingDBAttestation, 
        d: AttestationData)
    {
        && dbAttRecord.source_epoch == d.source.epoch
        && dbAttRecord.target_epoch == d.target.epoch
        && dbAttRecord.signing_root == Some(hash_tree_root(d))
    }
    
    // Given an attestation att and a slashing DB attestation dbAttRecord, 
    // check whether dbAttRecord is based on att.
    predicate method is_SlashingDBAtt_for_given_att(
        dbAttRecord: SlashingDBAttestation, 
        att: Attestation)
    {
        is_SlashingDBAtt_for_given_att_data(dbAttRecord, att.data)
    }

    // Given a set S of attestation shares and an attestastion att,
    // returns all shares in S that are based on att.
    function get_shares_in_set_based_on_given_att(
        S: set<AttestationShare>,
        att: Attestation
    ): set<AttestationShare>
    {
        var ret_set := set s: AttestationShare |
                                s in S && s.data == att.data :: s;

        ret_set
    }

    // Construct a slashing DB attestation for a given attestastion data
    function method construct_SlashingDBAttestation_from_att_data(attestation_data: AttestationData): SlashingDBAttestation
    {        
        var slashing_db_attestation := SlashingDBAttestation(
                                            source_epoch := attestation_data.source.epoch,
                                            target_epoch := attestation_data.target.epoch,
                                            signing_root := Some(hash_tree_root(attestation_data)));

        slashing_db_attestation
    }

    function method get_slot_from_slashing_db_attestation(a: SlashingDBAttestation): Slot
    requires exists att_data: AttestationData ::  a.signing_root == Some(hash_tree_root(att_data))
    {        
        hash_tree_root_properties<AttestationData>();
        var att_data: AttestationData :|  a.signing_root == Some(hash_tree_root(att_data));

        att_data.slot
    }

/*  // TODO: Prove post-condition
    method get_slashing_db_attestations_before_slot_s(
        db: set<SlashingDBAttestation>,
        s: Slot
    ) returns (S: set<SlashingDBAttestation>)
    requires ( forall r: SlashingDBAttestation | r in db :: 
                    ( exists att_data: AttestationData ::  r.signing_root == Some(hash_tree_root(att_data))
                    )
             )
    ensures ( forall a | a in S :: get_slot_from_slashing_db_attestation(a) < s)
    {           
        if db == {} 
        {
            S := {};
            assert ( forall a | a in S :: get_slot_from_slashing_db_attestation(a) < s);
        }
        else 
        {                
            var a: SlashingDBAttestation :| a in db;
            var T := get_slashing_db_attestations_before_slot_s(db - {a}, s);
            assert ( forall a | a in T :: get_slot_from_slashing_db_attestation(a) < s);
            if get_slot_from_slashing_db_attestation(a) < s 
            {                
                S := { a } + T;
                assert ( forall a | a in S :: get_slot_from_slashing_db_attestation(a) < s);
            }
            else 
            {
                S := T;
                assert ( forall a | a in S :: get_slot_from_slashing_db_attestation(a) < s);
            }                    
        }
*/

    ghost method get_slashing_db_attestations_before_slot_s(
        db: set<SlashingDBAttestation>,
        s: Slot
    ) returns (S: set<SlashingDBAttestation>)
    requires ( forall r: SlashingDBAttestation | r in db :: 
                    ( exists att_data: AttestationData ::  r.signing_root == Some(hash_tree_root(att_data))
                    )
             )
    ensures ( forall r | r in S :: 
                            && ( exists data: AttestationData ::  r.signing_root == Some(hash_tree_root(data)) )
                            && get_slot_from_slashing_db_attestation(r) < s)
    ensures ( forall r | r in db && r !in S :: 
                            && ( exists data: AttestationData ::  r.signing_root == Some(hash_tree_root(data)) )
                            && get_slot_from_slashing_db_attestation(r) >= s)
    {
        S := {};
        var unchecked := db;
        var checked := {};
        
        while unchecked != {}        
        invariant unchecked + checked == db
        invariant ( forall r: SlashingDBAttestation | r in S :: 
                                && ( exists data: AttestationData ::  r.signing_root == Some(hash_tree_root(data)) )
                                && get_slot_from_slashing_db_attestation(r) < s )
        invariant ( forall r: SlashingDBAttestation | r in checked && r !in S ::
                                && ( exists data: AttestationData ::  r.signing_root == Some(hash_tree_root(data)) )
                                && get_slot_from_slashing_db_attestation(r) >= s )                            
        decreases |unchecked|
        {
            var a: SlashingDBAttestation :| a in unchecked;
            unchecked := unchecked - {a};
            checked := checked + {a};

            hash_tree_root_properties<AttestationData>();
            var att_data: AttestationData :| a.signing_root == Some(hash_tree_root(att_data));
            if att_data.slot < s
            {
                S := S + {a};
            }
            else 
            {
                S := S;
            }            
        }             

        return S;
    }

    // Construct a slashing DB attestation for a given attestastion 
    function method construct_SlashingDBAttestation_from_att(att: Attestation): SlashingDBAttestation
    {        
        var slashing_db_attestation := construct_SlashingDBAttestation_from_att_data(att.data);

        slashing_db_attestation
    }
    // Given a set S of attestation and a slot s such that there exists only one attestation att 
    // such that att.data.slot == s. 
    // Returns att.
    function method get_attestation_with_given_slot(attSet: set<Attestation>, s: Slot): Attestation
    requires exists att: Attestation :: att in attSet && att.data.slot == s
    requires forall a1, a2: Attestation :: 
                && a1 in attSet 
                && a2 in attSet 
                && a1.data.slot == a2.data.slot
                        ==> a1 == a2
    {
        var ret_att: Attestation :| ret_att in attSet && ret_att.data.slot == s;

        ret_att
    }
    
    function method construct_SlashingDBAttestations_from_set_of_attestations(S: set<Attestation>): set<SlashingDBAttestation>
    {
        var ret_set := set att: Attestation |
                                att in S :: construct_SlashingDBAttestation_from_att_data(att.data);

        ret_set
    }

    predicate is_slashable_attestation_data_in_set_of_attestations(
        attSet: set<Attestation>, 
        attestation_data: AttestationData)
    {
        && var slashingDBAttestationSet := construct_SlashingDBAttestations_from_set_of_attestations(attSet);
        && is_slashable_attestation_data(slashingDBAttestationSet, attestation_data)
    }

    function f(n:nat): nat
    {
        if n > 0 then
            (n-1)/3
        else
            0
    }

    function quorum(n:nat):nat
    {
        if n > 0 then
            (2*n - 1)/3 + 1 
        else 
            0
    }

    predicate ByzThresholdAssumption(
        all_nodes: set<BLSPubkey>,
        honest_nodes: set<BLSPubkey>,
        dishonest_nodes: set<BLSPubkey>
    )
    {        
        && 2 * |dishonest_nodes| + 1 <= |honest_nodes|
        && all_nodes == honest_nodes + dishonest_nodes
        && honest_nodes * dishonest_nodes == {}
    }
}