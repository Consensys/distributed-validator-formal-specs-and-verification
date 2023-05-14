module Types 
{
    type ValidatorIndex = nat
    type Epoch = nat 
    type Slot = nat
    const SLOTS_PER_EPOCH := 32
    type {:extern "CommitteeIndex"} CommitteeIndex(!new, 0, ==)
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
        committees_at_slot: Slot,
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
        signing_root: Optional<Root>
    )

    datatype ProposerDuty = ProposerDuty(
        pubkey: BLSPubkey,
        validator_index: ValidatorIndex,
        slot: Slot        
    )

    datatype RandaoShare = RandaoShare(
        proposer_duty: ProposerDuty,
        slot: Slot,
        signing_root: Root,
        signature: BLSSignature
    )

    datatype BeaconBlock = BeaconBlock(
        slot: Slot,
        proposer_index: ValidatorIndex,
        parent_root: Root,
        state_root: Root,
        body: BeaconBlockBody
        // ... Other fields irrelevant to this spec
    )

    datatype BeaconBlockBody = BeaconBlockBody(
        attestations: seq<Attestation>,
        state_root: Root,
        randao_reveal: BLSSignature
        // ... Other fields irrelevant to this spec
    )

    datatype SignedBeaconBlock = SignedBeaconBlock(
        block: BeaconBlock,
        signature: BLSSignature
    )

    datatype SlashingDBBlock = SlashingDBBlock(        
        slot: Slot,
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

    datatype AttestationEvent = 
        | ServeAttestationDuty(attestation_duty: AttestationDuty)
        | AttConsensusDecided(id: Slot, decided_attestation_data: AttestationData)
        | ReceivedAttestationShare(attestation_share: AttestationShare)
        | ImportedNewBlock(block: BeaconBlock)
        | ResendAttestationShares
        | NoEvent

    datatype BlockEvent = 
        | ServeProposerDuty(proposer_duty: ProposerDuty)
        | BlockConsensusDecided(id: Slot, decided_beacon_block: BeaconBlock)
        | ReceiveRandaoShare(randao_share: RandaoShare)
        | ReceiveSignedBeaconBlock(block_share: SignedBeaconBlock)
        | ImportedNewBlock(block: BeaconBlock)       
        | ResendRandaoRevealSignatureShare
        | ResendBlockShare
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

    datatype AttestationConsensusValidityCheckState = AttestationConsensusValidityCheckState(
        attestation_duty: AttestationDuty,
        validityPredicate: AttestationData -> bool
    ) 

    datatype BlockConsensusValidityCheckState = BlockConsensusValidityCheckState(
        proposer_duty: ProposerDuty,
        randao_reveal: BLSSignature,
        validityPredicate: BeaconBlock -> bool
    )

    datatype DomainTypes = 
        | DOMAIN_BEACON_ATTESTER
        | DOMAIN_RANDAO
        | DOMAIN_BEACON_PROPOSER

    datatype RSState = RSState(
        pubkey: BLSPubkey
    ) 

    datatype BlockOutputs = BlockOutputs(
        sent_block_shares: set<MessaageWithRecipient<SignedBeaconBlock>>,
        sent_randao_shares: set<MessaageWithRecipient<RandaoShare>>,        
        submitted_data: set<SignedBeaconBlock>
    )

    datatype AttestationOutputs = AttestationOutputs(
        att_shares_sent: set<MessaageWithRecipient<AttestationShare>>,
        submitted_data: set<Attestation>
    )  

    datatype Adversary = Adversary(
        nodes: set<BLSPubkey>   
    )

    datatype AttestationDutyAndNode = AttestationDutyAndNode(
        attestation_duty: AttestationDuty,
        node: BLSPubkey
    )

    datatype ProposerDutyAndNode = ProposerDutyAndNode(
        proposer_duty: ProposerDuty,
        node: BLSPubkey
    )

    datatype DVAttestationEvent = 
        | AdversaryTakingStep(
                node: BLSPubkey, 
                new_attestation_shares_sent: set<MessaageWithRecipient<AttestationShare>>,
                messagesReceivedByTheNode: set<AttestationShare>
            )
        | HonestNodeTakingStep(
                node: BLSPubkey, 
                event: AttestationEvent, 
                nodeOutputs:  AttestationOutputs
            )

    datatype DVBlockEvent = 
        | AdversaryTakingStep(
                node: BLSPubkey, 
                new_sent_randao_shares: set<MessaageWithRecipient<RandaoShare>>,
                new_sent_block_shares: set<MessaageWithRecipient<SignedBeaconBlock>>,
                randaoShareReceivedByTheNode: set<RandaoShare>,
                blockShareReceivedByTheNode: set<SignedBeaconBlock>
            )
        | HonestNodeTakingStep(
                node: BLSPubkey, 
                event: BlockEvent, 
                nodeOutputs: BlockOutputs
            )
}

module Common_Functions{
    import opened Types
    import opened Set_Seq_Helper

    function method getOrDefault<T1,T2>(M:map<T1,T2>, key:T1, default:T2): T2
    {
        if key in M.Keys then
            M[key]
        else
            default
    }      

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

    function addRecepientsToMessage<M>(m: M, receipients: set<BLSPubkey>): (S: set<MessaageWithRecipient<M>>)
    {
        set r | r in receipients :: MessaageWithRecipient(message := m, receipient := r)
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

    function multicast<M>(m: M, receipients: set<BLSPubkey>): set<MessaageWithRecipient<M>>
    {
        addRecepientsToMessage(m, receipients)
    }

    function multicast_multiple<M>(ms: set<M>, receipients: set<BLSPubkey>): set<MessaageWithRecipient<M>>
    {
        var setWithRecipient := set m | m in ms :: addRecepientsToMessage(m, receipients);
        setUnion(setWithRecipient)
    }    

    function getEmptyBlockOuputs(): BlockOutputs
    {
        BlockOutputs(
            {},
            {},
            {}
        )
    }  

    function getEmptyAttestationOuputs(): AttestationOutputs
    {
        AttestationOutputs(
            {},
            {}
        )
    }  
}

module Set_Seq_Helper{
    function setUnion<T>(sets:set<set<T>>):set<T>
    {
        set s, e | s in sets && e in s :: e
    } 

    function seqToSet<T>(s: seq<T>): (r: set<T>)
    {
        set e | e in s
    }

    predicate uniqueSeq<T(==)>(s: seq<T>)
    {
        forall i, j | 0 <= i < |s| && 0 <= j < |s| :: s[i] == s[j] ==> i == j
    }

    lemma minOfSetOfSlotExists(s: set<int>)
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
            minOfSetOfSlotExists(sMinusE);
            var mMinusE :| mMinusE in sMinusE && forall e' | e' in sMinusE :: e' >= mMinusE;
        }    
    }

    
    function method {:opaque} minInSet(s: set<int>): (min: int)
    requires s != {}
    ensures min in s 
    ensures forall e | e in s :: min <= e 
    {
        existsMinOfNonemptySetOfInt(s);
        var e :| e in s && forall e' | e' in s :: e' >= e;
        e
    }

    function method {:opaque} maxInSet(s: set<int>): (max: int)
    requires s != {}
    ensures max in s 
    ensures forall e | e in s :: max >= e 
    {
        existsMaxOfNonemptySetOfInt(s);
        var e :| e in s && forall e' | e' in s :: e' <= e;
        e
    }   

    function seq_last<T>(s: seq<T>): T 
    requires |s| > 0 
    {
        s[|s|-1]
    }

    function method {:opaque} get_min(s: set<int>): (min: int)    
    requires s != {}
    ensures min in s
    ensures forall e | e in s :: min <= e
    {        
        minOfSetOfSlotExists(s);
        var e: int :| e in s && forall e' | e' in s :: e' >= e;
        e        
    }

    

    lemma ThingsIKnowAboutSubset<T>(x:set<T>, y:set<T>)
        requires x<y;
        ensures |x|<|y|;
    {
        if (x!={}) {
            var e :| e in x;
            ThingsIKnowAboutSubset(x-{e}, y-{e});
        }
    }

    lemma SubsetCardinality<T>(x:set<T>, y:set<T>)
        ensures x<y ==> |x|<|y|;
        ensures x<=y ==> |x|<=|y|;
    {
        if (x<y) {
            ThingsIKnowAboutSubset(x, y);
        }
        if (x==y) { // OBSERVE the other case
        }
    }

    lemma ItIsASingletonSet<T>(foo:set<T>, x:T)
        requires foo=={x};
        ensures |foo|==1;
    {
    }

    lemma ThingsIKnowAboutASingletonSet<T>(foo:set<T>, x:T, y:T)
        requires |foo|==1;
        requires x in foo;
        requires y in foo;
        ensures x==y;
    {
        if (x!=y) {
            assert {x} < foo;
            ThingsIKnowAboutSubset({x}, foo);
            assert |{x}| < |foo|;
            assert |foo|>1;
            assert false;
        }
    }

    predicate Injective<X(!new), Y(!new)>(f:X-->Y)
    reads f.reads;
    requires forall x :: f.requires(x);
    {
    forall x1, x2 :: f(x1) == f(x2) ==> x1 == x2
    }

    predicate InjectiveOver<X, Y>(xs:set<X>, ys:set<Y>, f:X-->Y)
    reads f.reads;
    requires forall x :: x in xs ==> f.requires(x);
    {
    forall x1, x2 :: x1 in xs && x2 in xs && f(x1) in ys && f(x2) in ys && f(x1) == f(x2) ==> x1 == x2
    }

    predicate InjectiveOverSeq<X, Y>(xs:seq<X>, ys:set<Y>, f:X->Y)
    reads f.reads;
    requires forall x :: x in xs ==> f.requires(x);
    {
    forall x1, x2 :: x1 in xs && x2 in xs && f(x1) in ys && f(x2) in ys && f(x1) == f(x2) ==> x1 == x2
    }

    lemma lem_MapSetCardinality<X, Y>(xs:set<X>, ys:set<Y>, f:X-->Y)
    requires forall x :: f.requires(x);
    requires Injective(f);
    requires forall x :: x in xs <==> f(x) in ys;
    requires forall y :: y in ys ==> exists x :: x in xs && y == f(x);
    ensures  |xs| == |ys|;
    {
    if (xs != {})
    {
        var x :| x in xs;
        var xs' := xs - {x};
        var ys' := ys - {f(x)};
        lem_MapSetCardinality(xs', ys', f);
    }
    }

    lemma lem_MapSetCardinalityOver<X, Y>(xs:set<X>, ys:set<Y>, f:X-->Y)
    requires forall x :: x in xs ==> f.requires(x);
    requires InjectiveOver(xs, ys, f);
    requires forall x :: x in xs ==> f(x) in ys;
    requires forall y :: y in ys ==> exists x :: x in xs && y == f(x);
    ensures  |xs| == |ys|;
    {
    if (xs != {})
    {
        var x :| x in xs;
        var xs' := xs - {x};
        var ys' := ys - {f(x)};
        lem_MapSetCardinalityOver(xs', ys', f);
    }
    }

    lemma lem_MapSubsetCardinalityOver<X, Y>(xs:set<X>, ys:set<Y>, f:X->Y)
    requires forall x :: x in xs ==> f.requires(x);
    requires InjectiveOver(xs, ys, f);
    requires forall x :: x in xs ==> f(x) in ys;
    ensures  |xs| <= |ys|;
    {
    if (xs != {})
    {
        var x :| x in xs;
        var xs' := xs - {x};
        var ys' := ys - {f(x)};
        lem_MapSubsetCardinalityOver(xs', ys', f);
    }
    }

    lemma lem_MapSubsetCardinalityOverNoInjective<T,T2>(s:set<T>, s2: set<T2>, f:T --> T2)
    requires forall m | m in s :: f.requires(m)
    requires s2 == set m | m in s :: f(m)
    requires |s| > 0 
    ensures |s2| > 0
    {
    var e :| e in s;

    assert f(e) in s2;
    }

    lemma lem_MapSubseqCardinalityOver<X, Y>(xs:seq<X>, ys:set<Y>, f:X->Y)
    requires forall x :: x in xs ==> f.requires(x);
    requires forall i, j :: 0 <= i < |xs| && 0 <= j < |xs| && i != j ==> xs[i] != xs[j];
    requires InjectiveOverSeq(xs, ys, f);
    requires forall x :: x in xs ==> f(x) in ys;
    ensures  |xs| <= |ys|;
    {
    if (xs != [])
    {
        var x := xs[0];
        var xs' := xs[1..];
        var ys' := ys - {f(x)};
        forall x' | x' in xs'
            ensures f(x') in ys';
        {
            assert x' in xs;
            assert f(x') in ys;
            if f(x') == f(x)
            {
                assert x in xs && x' in xs && f(x) in ys && f(x') in ys && f(x') == f(x);
                assert x' == x;
            }
        }
        forall x1, x2 | x1 in xs' && x2 in xs' && f(x1) in ys' && f(x2) in ys' && f(x1) == f(x2)
            ensures x1 == x2;
        {
            assert x1 in xs && x2 in xs && f(x1) in ys && f(x2) in ys';
        }
        lem_MapSubseqCardinalityOver(xs', ys', f);
    }
    }

    function MapSetToSet<X(!new), Y>(xs:set<X>, f:X->Y):set<Y>
    reads f.reads;
    requires forall x :: f.requires(x);
    requires Injective(f);
    ensures  forall x :: x in xs <==> f(x) in MapSetToSet(xs, f);
    ensures  |xs| == |MapSetToSet(xs, f)|;
    {
    var ys := set x | x in xs :: f(x); 
    lem_MapSetCardinality(xs, ys, f);
    ys
    }

    function MapSetToSetOver<X, Y>(xs:set<X>, f:X->Y):set<Y>
    reads f.reads;
    requires forall x :: x in xs ==> f.requires(x);
    requires InjectiveOver(xs, set x | x in xs :: f(x), f);
    ensures  forall x :: x in xs ==> f(x) in MapSetToSetOver(xs, f);
    ensures  |xs| == |MapSetToSetOver(xs, f)|;
    {
    var ys := set x | x in xs :: f(x); 
    lem_MapSetCardinalityOver(xs, ys, f);
    ys
    }

    function MapSeqToSet<X(!new), Y>(xs:seq<X>, f:X->Y):set<Y>
    reads f.reads;
    requires forall x :: f.requires(x);
    requires Injective(f);
    ensures  forall x :: x in xs <==> f(x) in MapSeqToSet(xs, f);
    {
    set x | x in xs :: f(x)
    }

    lemma lem_SubsetCardinality<X>(xs:set<X>, ys:set<X>, f:X->bool)
    requires forall x :: x in xs ==> f.requires(x);
    requires forall x :: x in ys ==> x in xs && f(x);
    ensures  |ys| <= |xs|;
    {
    if (ys != {})
    {
        var y :| y in ys;
        var xs' := xs - {y};
        var ys' := ys - {y};
        lem_SubsetCardinality(xs', ys', f);
    }
    }

    function MakeSubset<X(!new)>(xs:set<X>, f:X->bool):set<X>
    reads f.reads;
    requires forall x :: x in xs ==> f.requires(x);
    ensures  forall x :: x in MakeSubset(xs, f) <==> x in xs && f(x);
    ensures  |MakeSubset(xs, f)| <= |xs|;
    {
    var ys := set x | x in xs && f(x);
    lem_SubsetCardinality(xs, ys, f);
    ys
    }

    /* examples:
    function{:opaque} setAdd1(xs:set<int>):set<int>
    ensures forall x :: x in xs <==> x + 1 in setAdd1(xs);
    ensures |xs| == |setAdd1(xs)|;
    {
    MapSetToSet(xs, x => x + 1)
    }
    function{:opaque} setPos(xs:set<int>):set<int>
    ensures forall x :: x in setPos(xs) <==> x in xs && x > 0;
    {
    MakeSubset(xs, x => x > 0)
    }
    */

    lemma lem_UnionCardinality<X>(xs:set<X>, ys:set<X>, us:set<X>)
        requires us==xs+ys;
        ensures |us| >= |xs|;
        decreases ys;
    {
        if (ys=={}) {
        } else {
            var y :| y in ys;
            if (y in xs) {
                var xr := xs - {y};
                var yr := ys - {y};
                var ur := us - {y};
                lem_UnionCardinality(xr, yr, ur);
            } else {
                var ur := us - {y};
                var yr := ys - {y};
                lem_UnionCardinality(xs, yr, ur);
            }
        }
    }

    function SetOfNumbersInRightExclusiveRange(a:int, b:int):set<int>
        requires a <= b;
        ensures forall opn :: a <= opn < b ==> opn in SetOfNumbersInRightExclusiveRange(a, b);
        ensures forall opn :: opn in SetOfNumbersInRightExclusiveRange(a, b) ==> a <= opn < b;
        ensures |SetOfNumbersInRightExclusiveRange(a, b)| == b-a;
        decreases b-a;
    {
        if a == b then {} else {a} + SetOfNumbersInRightExclusiveRange(a+1, b)
    }

    lemma lem_CardinalityOfBoundedSet(s:set<int>, a:int, b:int)
        requires forall opn :: opn in s ==> a <= opn < b;
        requires a <= b;
        ensures  |s| <= b-a;
    {
        var range := SetOfNumbersInRightExclusiveRange(a, b);
        forall i | i in s
            ensures i in range;
        {
        }
        assert s <= range;
        SubsetCardinality(s, range);
    }


    function intsetmax(s:set<int>):int
        requires |s| > 0;
        ensures  var m := intsetmax(s);
                m in s && forall i :: i in s ==> m >= i;
    {
        var x :| x in s;
        if |s| == 1 then
            assert |s - {x}| == 0;
            x
        else
            var sy := s - {x};
            var y := intsetmax(sy);
            assert forall i :: i in s ==> i in sy || i == x;
            if x > y then x else y
    }

    lemma lemmDoubleIntersections<T(==)>(S1:set<T>, S2:set<T>, S3:set<T>)
    requires S1 * S2 * S3 != {}
    ensures exists m: T :: m in S1 && m in S2 && m in S3
    {

    }

    lemma lemmaEmptyIntersectionImpliesDisjointness<T>(
      s1: set<T>,
      s2: set<T>
    )
    requires s1 * s2 == {}
    ensures s1 !! s2 
    {
      if s1 == {} && s2 == {}
      {
        assert s1 !! s2 ;
      }
      else if s1 == {} 
      {
        assert s1 !! s2 ;
      }  
      else if s2 == {} 
      {
        assert s1 !! s2 ;
      }           
      else if !(s1 !! s2)
      {
        var e :| e in s1 && e in s2;
        assert e in (s1 * s2);
        assert (s1 * s2) != {};
        assert false;
      }
    }

    lemma lemmaInUnion<T(==)>(S: set<T>, S1: set<T>, S2: set<T>, m: T)
    requires S == S1 + S2
    requires m in S
    ensures m in S1 || m in S2
    {}

    lemma lemmaInUnionOneElement<T(==)>(S: set<T>, S1: set<T>, m1: T, m2: T)
    requires S == S1 + {m1}
    requires m2 in S
    ensures m2 in S1 || m2 == m1
    {}    

    lemma lemmaMapKeysHasOneEntryInItems<K, V>(m: map<K, V>, k: K)  
    requires k in m.Keys
    ensures exists i :: i in m.Items && i.0 == k 
    {
        assert (k, m[k]) in m.Items;
    }       

    lemma lemmaFromMemberToSingletonSet<T>(e: T, S: set<T>)
    requires e in S
    ensures {e} <= S
    {}

    lemma lemmaUnionOfSubsets<T>(S1: set<T>, S2: set<T>, S: set<T>)
    requires S1 <= S && S2 <= S
    ensures S1 + S2 <= S
    {}

    lemma lemmaSubsetOfSubset<T>(S1: set<T>, S2: set<T>, S3: set<T>)
    requires S1 <= S2 && S2 <= S3
    ensures S1  <= S3
    {}

    lemma lem_member_of_subset_is_member_of_superset<T>(m: T, S1: set<T>, S2: set<T>)
    requires m in S1
    requires S1 <= S2 
    ensures  m in S2
    {}

    lemma lem_union_with_subset_is_unchanged<T>(S1: set<T>, S2: set<T>)
    requires S1 <= S2 
    ensures  S1 + S2 == S2
    {}

    lemma lem_union_with_empty_set_is_unchanged<T>(S1: set<T>, S2: set<T>, S: set<T>)
    requires && S1 == {}
             && S1 + S2 == S   
    ensures  S == S2
    {}

    lemma lemmaSingletonSetToMembership<T>(e: T, S: set<T>)
    requires {e} == S
    ensures e in S
    {}

    lemma existsMinOfNonemptySetOfInt(s: set<int>)
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
            existsMinOfNonemptySetOfInt(sMinusE);
            var mMinusE :| mMinusE in sMinusE && forall e' | e' in sMinusE :: e' >= mMinusE;
        }    
    }  

    lemma existsMaxOfNonemptySetOfInt(s: set<int>)
    requires s != {}
    ensures exists max :: 
                        && max in s 
                        && forall e | e in s :: max >= e 
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
            existsMaxOfNonemptySetOfInt(sMinusE);
            var mMinusE :| mMinusE in sMinusE && forall e' | e' in sMinusE :: e' <= mMinusE;
        }    
    }       
}

module Signing_Methods{
    import opened Types
    import opened Set_Seq_Helper

    function method compute_start_slot_at_epoch(epoch: Epoch): Slot
    {
        epoch * SLOTS_PER_EPOCH
    }   

    // TODO: What about the genesis_validator_root parameter?
    function method {:extern} compute_domain(
        domain_type: DomainTypes,
        fork_version: Version
    ): (domain: Domain)

    function method {:extern} compute_signing_root<T>(
        data: T,
        domain: Domain
    ): Root

    // TODO: Fix Python code to match the following (Python code uses epoch)
    function method compute_attestation_signing_root(attestation_data: AttestationData, fork_version: Version): Root
    {
        var domain := compute_domain(DOMAIN_BEACON_ATTESTER, fork_version);
        compute_signing_root(attestation_data, domain)
    }

    function method {:extern} hash_tree_root<T>(data: T): Root 

    function method get_target_epochs(att_slashing_db: set<SlashingDBAttestation>): (target_epochs: set<nat>)
    requires att_slashing_db != {}
    ensures target_epochs != {}
    {
        var target_epochs := set att | att in att_slashing_db :: att.target_epoch;
        assert var e :| e in att_slashing_db; e.target_epoch in target_epochs;
        target_epochs
    }

    function method get_source_epochs(att_slashing_db: set<SlashingDBAttestation>): (source_epochs: set<nat>)
    requires att_slashing_db != {}
    ensures source_epochs != {}
    {
        var source_epochs := set att | att in att_slashing_db :: att.source_epoch;
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
            var min_target := minInSet(get_target_epochs(att_slashing_db));
            var min_source := minInSet(get_source_epochs(att_slashing_db));
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
                exists past_att | past_att in att_slashing_db ::
                        || is_slashable_attestation_pair(past_att, slashing_db_att_for_att_data)
                        || is_slashable_attestation_pair(slashing_db_att_for_att_data, past_att)
        else
            false        
    } by method 
    {
        // Check for EIP-3076 conditions:
        // https://eips.ethereum.org/EIPS/eip-3076#conditions
        if att_slashing_db != {} 
        {
            var min_target := minInSet(get_target_epochs(att_slashing_db));
            var min_source := minInSet(get_source_epochs(att_slashing_db));
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
                var atts_to_check := att_slashing_db;
                var slashing_db_att_for_att_data := 
                    SlashingDBAttestation(
                        source_epoch := attestation_data.source.epoch,
                        target_epoch := attestation_data.target.epoch,
                        signing_root := None
                    );
                while atts_to_check != {}
                invariant var checked := att_slashing_db - atts_to_check;
                        forall a | a in checked :: 
                            && !is_slashable_attestation_pair(a, slashing_db_att_for_att_data)
                            && !is_slashable_attestation_pair(slashing_db_att_for_att_data, a)
                {
                        var past_att :| past_att in atts_to_check;
                        if || is_slashable_attestation_pair(past_att, slashing_db_att_for_att_data)
                           || is_slashable_attestation_pair(slashing_db_att_for_att_data, past_att)
                        {
                            assert is_slashable_attestation_data(att_slashing_db, attestation_data);
                            return true;
                        }

                        atts_to_check := atts_to_check - {past_att};
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

    predicate method ci_decision_is_valid_attestation_data(
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

    function method construct_SlashingDBAttestation_from_att_data(attestation_data: AttestationData): SlashingDBAttestation
    {        
        var slashing_db_attestation := SlashingDBAttestation(
                                            source_epoch := attestation_data.source.epoch,
                                            target_epoch := attestation_data.target.epoch,
                                            signing_root := Some(hash_tree_root(attestation_data)));

        slashing_db_attestation
    }

    function method construct_SlashingDBAttestation_from_att(att: Attestation): SlashingDBAttestation
    {        
        var slashing_db_attestation := construct_SlashingDBAttestation_from_att_data(att.data);

        slashing_db_attestation
    }

    function method f_construct_aggregated_attestation_for_new_attestation_share(
        attestation_share: AttestationShare, 
        k: (AttestationData, seq<bool>),
        construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>, 
        rcvd_attestation_shares: map<Slot,map<(AttestationData, seq<bool>), set<AttestationShare>>>
    ): (aggregated_attestation: Attestation)
    requires attestation_share.data.slot in rcvd_attestation_shares.Keys
    requires k in rcvd_attestation_shares[attestation_share.data.slot]
    requires construct_signed_attestation_signature(rcvd_attestation_shares[attestation_share.data.slot][k]).isPresent()    
    ensures aggregated_attestation.data == attestation_share.data
    {
        Attestation(
            aggregation_bits := attestation_share.aggregation_bits,
            data := attestation_share.data,
            signature := construct_signed_attestation_signature(rcvd_attestation_shares[attestation_share.data.slot][k]).safe_get()
        )
    }
    
    function method get_slashing_slots(slashing_db: set<SlashingDBBlock>): (slots_in_db: set<int>)    
    requires slashing_db != {}
    ensures slots_in_db != {}    
    {
        var slots_in_db := set block | block in slashing_db :: block.slot;
        assert var e :| e in slashing_db; e.slot in slots_in_db;
        slots_in_db
    }

    // is_slashable_block is for line 153 in helpers.py
    predicate is_slashable_block(
        block_slashing_db: set<SlashingDBBlock>,
        block: BeaconBlock
    ) 
    {
        if block_slashing_db != {} then
        
            var slots := get_slashing_slots(block_slashing_db);
            var min_slot := get_min(slots);

            if block.slot < min_slot then
                true
            else 
                if exists db_block :: 
                        && db_block in block_slashing_db
                        && block.slot == db_block.slot 
                        && db_block.signing_root.isPresent()
                        && hash_tree_root(block) != db_block.signing_root.safe_get()
                then 
                    true
                else
                    false
        else 
            false
    } by method
    {            
        
        if block_slashing_db != {}
        {
            var slots := get_slashing_slots(block_slashing_db);
            var min_slot := get_min(slots);

            if block.slot < min_slot 
            {
                return true;
            }
            
            if exists db_block ::   && db_block in block_slashing_db  
                                    && block.slot == db_block.slot
                                    && db_block.signing_root.isPresent()
                                    && hash_tree_root(block) != db_block.signing_root.safe_get()
            {
                return true;
            }
        }
        
        return false;            
    }    
    
    predicate method ci_decision_is_valid_beacon_block(
        block_slashing_db: set<SlashingDBBlock>,
        block: BeaconBlock,
        proposer_duty: ProposerDuty,
        complete_signed_randao_reveal: BLSSignature
    )    
    {
        && block.slot == proposer_duty.slot 
        && block.body.randao_reveal == complete_signed_randao_reveal
        && !is_slashable_block(block_slashing_db, block)
    }

    function method compute_epoch_at_slot(slot: Slot): Epoch
    {
        slot / SLOTS_PER_EPOCH
    }   

    function method {:extern} compute_domain_with_epoch(
        domain_type: DomainTypes,
        epoch: Epoch
    ): (domain: Domain)

    function method {:extern} compute_domain_with_fork_version(
        domain_type: DomainTypes,
        fork_version: Version
    ): (domain: Domain)

    function method compute_randao_reveal_signing_root(slot: Slot): Root
    {   
        var epoch := compute_epoch_at_slot(slot);
        var domain := compute_domain_with_epoch(DOMAIN_RANDAO, epoch);
        compute_signing_root(epoch, domain)
    }
    
    function method compute_block_signing_root(block: BeaconBlock): Root
    {
        var epoch := compute_epoch_at_slot(block.slot);
        var domain := compute_domain_with_epoch(DOMAIN_BEACON_PROPOSER, epoch);
        compute_signing_root(block, domain)
    }  

    function method construct_SlashingDBBlock_from_beacon_block(block: BeaconBlock
    ): (slashing_db_block: SlashingDBBlock)
    ensures slashing_db_block == SlashingDBBlock(block.slot, Some(hash_tree_root(block)))
    ensures slashing_db_block.slot == block.slot
    ensures && slashing_db_block.signing_root.isPresent()
            && slashing_db_block.signing_root.safe_get() == hash_tree_root(block)
    {   
        var slot := block.slot;
        var signing_root := hash_tree_root(block);
        var slashing_db_block := SlashingDBBlock(
                                            slot := slot,                                            
                                            signing_root := Some(signing_root)
                                );

        slashing_db_block
    }  
}