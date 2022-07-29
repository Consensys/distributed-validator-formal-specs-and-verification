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

    

    // consensus_is_valid_block is for line 174
    /*
    method consensus_is_valid_block(
        block_slashing_db: set<SlashingDBBlock>,
        block: BeaconBlock,
        proposer_duty: ProposerDuty,
        complete_signed_randao_reveal: BLSSignature)
    returns (b: bool) 
    {
        // TODO: Add correct block.proposer_index check
        var slashable: bool;
        slashable := is_slashable_block(block_slashing_db, block, proposer_duty.pubkey);
        b := block.slot == proposer_duty.slot &&            
             block.body.randao_reveal == complete_signed_randao_reveal &&
             !slashable;                 
    }
    */
    predicate method consensus_is_valid_block(
        block_slashing_db: set<SlashingDBBlock>,
        block: BeaconBlock,
        proposer_duty: ProposerDuty,
        complete_signed_randao_reveal: BLSSignature)
    
    {
        // TODO: Add correct block.proposer_index check        
        && block.slot == proposer_duty.slot 
        && block.body.randao_reveal == complete_signed_randao_reveal
        && !is_slashable_block(block_slashing_db, block, proposer_duty.pubkey)
    }

    // 
    function method get_slashing_slots(slashing_db: BlockSlashingDB): (slots_in_db: set<int>)    
    requires slashing_db != {}
    ensures slots_in_db != {}    
    {
        var slots_in_db := set block | block in slashing_db :: block.slot;
        assert var e :| e in slashing_db; e.slot in slots_in_db;
        slots_in_db
    }

    // NOTE: Left this method here just in case, but it is currently not being used anywhere.
    // function method get_slashing_blocks_with_slot(
    //     slashing_db: BlockSlashingDB, 
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
        block: BeaconBlock, 
        pubkey: BLSPubkey
    ) 
    {
        if block_slashing_db != {} then
        
            var slots := get_slashing_slots(block_slashing_db);
            var min_slot := get_min(slots);

            if block.slot < min_slot then
                true
            else 
                if exists db_block :: db_block in block_slashing_db && 
                                      block.slot == db_block.slot &&
                                      hash_tree_root(block) != db_block.signing_root
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
            
            if exists db_block :: db_block in block_slashing_db && 
                                    block.slot == db_block.slot &&
                                    hash_tree_root(block) != db_block.signing_root
            {
                return true;
            }
        }
        
        return false;            
    }     

}