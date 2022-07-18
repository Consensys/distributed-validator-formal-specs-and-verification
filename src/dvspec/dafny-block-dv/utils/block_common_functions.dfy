include "./block_types.dfy"

module BlockCommonFunctions{
    import opened BlockTypes

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

    function method compute_epoch_at_slot(slot: Slot): Epoch
    {
        slot / SLOTS_PER_EPOCH
    }   

    function method {:extern} compute_domain(
        domain_type: DomainTypes,
        epoch: Epoch
    ): (domain: Domain)

    
    predicate uniqueSeq<T>(s: seq<T>)
    {
        forall i, j | 0 <= i < |s| && 0 <= j < |s| :: s[i] == s[j] ==> i == j
    }

    predicate method {:extern} verify_bls_siganture<T>(
        data: T,
        signature: BLSSignature,
        pubkey: BLSPubkey
    )

    function method {:extern} hash_tree_root<T>(data: T): Root 

    function getMessagesFromMessagesWithRecipient<M>(mswr: set<MessaageWithRecipient<M>>): set<M>
    {
        set mwr | mwr in mswr :: mwr.message
    }
   

    /*
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
    */

    function wrapMessagesWithRecipient<M>(sm: set<M>, r: BLSPubkey): set<MessaageWithRecipient<M>>
    {
        set m | m in sm :: MessaageWithRecipient(
            message :=  m,
            receipient := r
        )
    }

    function wrapMessageWithRecipients<M>(m: M, receipients: set<BLSPubkey>): set<MessaageWithRecipient<M>>
    {
        set r | r in receipients :: MessaageWithRecipient(message := m, receipient := r)
    }

    function setUnion<T>(sets:set<set<T>>):set<T>
    {
        set s, e | s in sets && e in s :: e
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

    function method {:opaque} get_min(s: set<int>): (min: int)    
    requires s != {}
    ensures min in s
    ensures forall e | e in s :: min <= e
    {        
        minOfSetOfSlotExists(s);
        var e: int :| e in s && forall e' | e' in s :: e' >= e;
        e        
    }
}