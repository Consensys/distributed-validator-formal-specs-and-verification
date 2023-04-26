include "./block_types.dfy"

module Block_Common_Functions{
    import opened Block_Types

    function method getOrDefault<T1,T2>(M:map<T1,T2>, key:T1, default:T2): T2
    {
        if key in M.Keys then
            M[key]
        else
            default
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

    function seq_last<T>(s: seq<T>): T 
    requires |s| > 0 
    {
        s[|s|-1]
    }

    function method compute_start_slot_at_epoch(epoch: Epoch): Slot
    {
        epoch * SLOTS_PER_EPOCH
    }   

    function method compute_epoch_at_slot(slot: Slot): Epoch
    {
        slot / SLOTS_PER_EPOCH
    }   

    function method {:extern} compute_domain_with_epoch(
        domain_type: DomainTypes,
        epoch: Epoch
    ): (domain: Domain)

    // TODO: What about the genesis_validator_root parameter?
    function method {:extern} compute_domain_with_fork_version(
        domain_type: DomainTypes,
        fork_version: Version
    ): (domain: Domain)
    
    predicate uniqueSeq<T>(s: seq<T>)
    {
        forall i, j | 0 <= i < |s| && 0 <= j < |s| :: s[i] == s[j] ==> i == j
    }

    function method {:extern} hash_tree_root<T>(data: T): Root 

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

    // 
    function method get_slashing_slots(slashing_db: set<SlashingDBBlock>): (slots_in_db: set<int>)    
    requires slashing_db != {}
    ensures slots_in_db != {}    
    {
        var slots_in_db := set block | block in slashing_db :: block.slot;
        assert var e :| e in slashing_db; e.slot in slots_in_db;
        slots_in_db
    }

    // NOTE: Left this method here just in case, but it is currently not being used anywhere.
    // function method get_slashing_blocks_with_slot(
    //     slashing_db: set<SlashingDBBlock>, 
    //     slot: Slot
    // ): (slashing_blocks: set<SlashingDBBlock>)    
    // requires slashing_db != {}        
    // {
    //     var slashing_blocks := set block | block in slashing_db && block.slot == slot :: block;            
    //     slashing_blocks
    // }

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

    lemma lemmaOnGetMessagesFromMessagesWithRecipientWhenAllMessagesAreTheSame<M>(
        messagesToBeSent: set<MessaageWithRecipient<M>>,
        message: M
    )
    requires forall m | m in messagesToBeSent :: m.message == message 
    requires messagesToBeSent != {}
    ensures getMessagesFromMessagesWithRecipient(messagesToBeSent) ==  {message}
    { }

    lemma lemmaImaptotalElementInDomainIsInKeys<K(!new), V>(m: imaptotal<K, V>, e: K)
    ensures e in m.Keys
    { }

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

    predicate method is_slashable_pair_of_beacon_blocks(
        block_1: SlashingDBBlock, 
        block_2: SlashingDBBlock)
    {
        && block_1.slot == block_2.slot
        && block_1.signing_root.isPresent()
        && block_2.signing_root.isPresent()
        && block_1.signing_root.safe_get() != block_2.signing_root.safe_get()
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